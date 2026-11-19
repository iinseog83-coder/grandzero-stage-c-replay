#!/usr/bin/env python3
"""
GRANDZERO Ω — Stage C (Finite Rational Cellular Sheaf & Global Consistency Gate)
Hardened External Replay Verifier (`verify_stage_c_external_replay.py`)
================================================================================
Enforces an 8-boolean fail-closed conjunction (`ExternalReplayPass`):
  1. `pre_pins_ok`        : Fail-fast ZIP size + SHA-256 + 22/22 internal file pins + no `.lake`
  2. `stage_a_lineage_ok` : All 6 vendored `StageA` files match Stage A Final Closure SHA-256s
  3. `stage_b_lineage_ok` : All 6 vendored `StageB` files match Stage B Final Closure SHA-256s
  4. `exact_4331`         : Exact Lean 4.33.1 (`commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6`)
  5. `clean_build_pass`   : Cold `lake build` exit code 0 in isolated temporary directory (0 warnings)
  6. `audit_vectors_pass` : `lake exe stage_c_audit` exit code 0 + field-by-field match on all 10
                            `VECTOR|ID=TC-01..TC-07b` rows + 2 `EXTRA|...` rows + final banner
  7. `axiom_audit_pass`   : `#check` & `#print axioms` on all 62 `GrandZero.StageC` theorems using ONLY
                            `{propext, Classical.choice, Quot.sound}` + 0 forbidden tokens in source
  8. `source_identity_pass`: Post-build 22/22 source files + original ZIP SHA-256 unchanged
"""

import datetime
import hashlib
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE_NAME = "GRANDZERO_STAGE_C_SHEAF_Q0_CLEANROOM_SOURCE_ARCHIVE.zip"
EXPECTED_ARCHIVE_SIZE = 98749
EXPECTED_ARCHIVE_SHA256 = "4bfda01b3c6dddec215ee1d9aac39da43d30a0d20212731a6ff6ac7571a81388"
EXPECTED_LEAN_VERSION_SUBSTR = "4.33.1"
EXPECTED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

STAGE_A_FROZEN_LIB_PINS = {
    "StageA.lean": "15592e37e2bf4db61de644e33ab8c2d69ce20949021401996c9e3495b3b586fb",
    "StageA/Q0SyntaxAndUnits.lean": "04ec42ab65c6db2192c7bc5b04010c840f5d61c1e1abdc49f938fe6a645ad807",
    "StageA/Q0PartialSemantics.lean": "3a4e83073c7b2633f86d24dc67bb8b8f9c6731a0d73d09aa35c8fb9478c90469",
    "StageA/Q0ValidTape.lean": "9bc851eb9d938972caac2e77af9d1ecf41009393fc2ff43e37b4535ccd06eade",
    "StageA/Q0GuardedReflection.lean": "aad43e6c1dceeec4bea83781a76b77ccf38926a52003dea296d08f3517035fc9",
    "StageA/Q0BipolarKernel.lean": "bb59274b895c5022741c0e3bb4949ef03881db5f42ad552f52fd634838b31593",
}

STAGE_B_FROZEN_LIB_PINS = {
    "StageB.lean": "5a6dccc49c622a5bea64458e1ec31c2226fe0370cb1706f9fadeb5fe8a4eab4e",
    "StageB/Q0ContextAndParallelSubst.lean": "61706fce236b9c38eed04745ad9bf2b1623fc4be45a3d0aa88940fd60213dc6d",
    "StageB/Q0TypedTransportAndPullback.lean": "be4c83d11152938650ca16eb132e4653d76dfd70dfe06a57f970a52fdc21f379",
    "StageB/Q0ConeEmptyOverlap.lean": "69deb1f7f3d223481bc89c206c0406fa8ddeb66b6e91896befe4336bbe70e270",
    "StageB/Q0Triangle2CellKernel.lean": "4aa4def7d68afb59b08a10d995a53976f38434ac6d1876cf0c07856eb46c0166",
    "StageB/Q0StageBAdversarialVectors.lean": "b192e577396da2766bb5589196431b77576f2b931b6a46ea2d3317ea127ef5b7",
}

EXPECTED_FILE_PINS = {
    **STAGE_A_FROZEN_LIB_PINS,
    **STAGE_B_FROZEN_LIB_PINS,
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.lean": "954e13a0b916b7f580589b3529919edce619038a68fafc99f5093a97a05c6c99",
    "lake-manifest.json": "6543a16dc054e7e943a8535d49bc076ca01df0607575e1ce8a9083e55a497a56",
    "StageC.lean": "73c95ed973230e8a2c3fcf229af430c728023041911c1420e92cf71eeb16b899",
    "StageC/Q0RationalMatrixAndRankNullity.lean": "6bf3a75d45ccac609abce0546a83585b37aac3e34dbb15b2f3da2af2299b813c",
    "StageC/Q0CellularComplexAndSheaf.lean": "c48c81aea4a3c97442bd89fb94f3820d410c4d1149babcc7a2973ce469a53364",
    "StageC/Q0CohomologyAndH1Quotient.lean": "5956b9b8b5259dd985d306dfe05535bfaf01bd4fcc871d88574c9694d3212041",
    "StageC/Q0AffineStageBBridgeAndGlobalGate.lean": "3659e9ea1f98239581b6c05c29b1a641f0902120d7252c80a42b14b3fc75b49f",
    "StageC/Q0StageCAdversarialVectors.lean": "caa47d533b66eab5f9ebaaf3d4ffc09e26a05b377f7aed8013610efc724c5792",
    "Main.lean": "6c2db421228b749230a4e5c197bb1b81f70945193f57925602df2786b5d1cd78",
}

EXPECTED_VECTOR_VERDICTS = {
    "TC-01": "verifiedCompatGlobalSection(h0=1,h1=0)",
    "TC-02": "verifiedCohomologyObstruction(h0=1,h1=1)",
    "TC-03": "verifiedFaceCurvatureFailure(h0=1,h1=0)",
    "TC-04a": "verifiedAnchorOrGuardIncompatibility(h0=1,h1=0)",
    "TC-04b": "verifiedAnchorOrGuardIncompatibility(h0=1,h1=0)",
    "TC-05a": "rejectedInvalidComplexOrSheaf(boundaryNotNilpotent)",
    "TC-05b": "rejectedInvalidComplexOrSheaf(nonFunctorialSheafRestriction)",
    "TC-06": "rejectedInvalidCertificate",
    "TC-07a": "rejectedInvalidComplexOrSheaf(illTypedStalkOrMatrix)",
    "TC-07b": "rejectedInvalidComplexOrSheaf(authorityEscalation)",
}

THEOREMS_62 = [
    # C-1: Q0RationalMatrixAndRankNullity (33 theorems)
    "allFin_iff",
    "vecEqBool_iff",
    "matEqBool_iff",
    "finSum_ext",
    "finSum_zero",
    "finSum_add",
    "finSum_mul_left",
    "finSum_mul_right",
    "finSum_comm",
    "finSum_delta_left",
    "finSum_delta_right",
    "vecToList_length",
    "vecToList_getElem",
    "matVec_zero",
    "zeroMat_vec",
    "idMat_vec",
    "addVec_zero_left",
    "addVec_zero_right",
    "matVec_add",
    "addMat_vec",
    "matVec_matMul",
    "matMul_assoc",
    "matMul_id_left",
    "matMul_id_right",
    "matMul_zero_right",
    "matMul_zero_left",
    "matMul_add_right",
    "matMul_add_left",
    "dotVec_zero_left",
    "dotVec_matVec_transpose",
    "thm_dual_obstruction_not_in_image",
    "thm_rank_nullity_cert_kernel_exact",
    "thm_rank_nullity_cert_image_exact",
    # C-2: Q0CellularComplexAndSheaf (6 theorems)
    "blockOffset_add_lt",
    "extractVertexList_length",
    "thm_sheaf_flag_functorial_sound",
    "thm_sheaf_functorial_imp_nilpotent",
    "thm_cochain_nilpotent_sound",
    "thm_stageC_global_authority_meet_nonescalation",
    # C-3: Q0CohomologyAndH1Quotient (2 theorems)
    "thm_h0_basis_exact",
    "thm_h1_quotient_decomp_unique",
    # C-4: Q0AffineStageBBridgeAndGlobalGate (10 theorems)
    "thm_exact_affine_bridge_sound",
    "lem_checkInGlobalSolutionSet_iff",
    "matVec_vertexSelectorMat",
    "thm_stageC_anchor_guard_unsat_sound",
    "thm_stageC_structural_invalid_universal",
    "lem_validateSheaf_none_unpack",
    "thm_stageC_compat_section_sound",
    "thm_stageC_cohomology_obstruction_sound_and_exclusive",
    "thm_stageC_face_curvature_sound_and_exclusive",
    "thm_stageC_incompatibility_sound_and_exclusive",
    # C-5: Q0StageCAdversarialVectors (11 theorems)
    "tc01_filled_triangle_compat_global_section",
    "tc01_stageB_affine_vs_nonlinear_gate",
    "tc02_hollow_cycle_cohomology_obstruction",
    "tc03_filled_triangle_face_curvature_failure",
    "tc04a_anchor_farkas_incompatibility",
    "tc04b_guard_domain_incompatibility",
    "tc05a_boundary_sign_flip_rejected",
    "tc05b_nonfunctorial_sheaf_rejected",
    "tc06_forged_cohomology_dim_rejected",
    "tc07a_ill_typed_torque_matrix_rejected",
    "tc07b_authority_escalation_rejected",
]


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1048576), b""):
            h.update(chunk)
    return h.hexdigest()


def read_os_release() -> str:
    if os.path.isfile("/etc/os-release"):
        try:
            with open("/etc/os-release", "r", encoding="utf-8") as f:
                for line in f:
                    if line.startswith("PRETTY_NAME="):
                        return line.split("=", 1)[1].strip().strip('"')
        except OSError:
            pass
    return platform.platform()


def find_bin(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    elan_candidate = os.path.join(os.path.expanduser("~"), ".elan", "bin", name)
    if os.path.isfile(elan_candidate):
        return elan_candidate
    if os.path.isfile(elan_candidate + ".exe"):
        return elan_candidate + ".exe"
    raise FileNotFoundError(f"Required executable `{name}` not found on PATH or ~/.elan/bin")


def strip_lean_comments(src: str) -> str:
    out = []
    i = 0
    n = len(src)
    block_depth = 0
    in_str = False
    while i < n:
        if block_depth > 0:
            if src[i : i + 2] == "/-":
                block_depth += 1
                i += 2
            elif src[i : i + 2] == "-/":
                block_depth -= 1
                i += 2
            else:
                i += 1
        elif in_str:
            if src[i] == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif src[i] == '"':
                in_str = False
                out.append('"')
                i += 1
            else:
                out.append(" ")
                i += 1
        else:
            if src[i : i + 2] == "/-":
                block_depth = 1
                i += 2
            elif src[i : i + 2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True
                out.append('"')
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)


def safe_extract_zip(zip_path: str, dest_dir: str) -> list[str]:
    dest_real = os.path.realpath(dest_dir)
    extracted = []
    with zipfile.ZipFile(zip_path, "r") as zf:
        for info in zf.infolist():
            rel_name = info.filename
            if info.is_dir():
                raise ValueError(f"Unexpected directory entry in archive: {rel_name}")
            if os.path.isabs(rel_name) or "\\" in rel_name:
                raise ValueError(f"Illegal path format in archive: {rel_name}")
            parts = rel_name.split("/")
            if any(p in ("", ".", "..") for p in parts):
                raise ValueError(f"Path traversal attempt in archive: {rel_name}")
            unix_mode = info.external_attr >> 16
            if (unix_mode & 0o170000) == 0o120000:
                raise ValueError(f"Symlink entry forbidden in archive: {rel_name}")

            target_path = os.path.realpath(os.path.join(dest_real, *parts))
            if os.path.commonpath([dest_real, target_path]) != dest_real:
                raise ValueError(f"Zip-Slip path escape blocked: {rel_name}")

            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            with zf.open(info, "r") as src, open(target_path, "wb") as dst:
                shutil.copyfileobj(src, dst)
            extracted.append(rel_name)
    return sorted(extracted)


def verify_structured_vectors(stdout_text: str) -> tuple[bool, list[str]]:
    errors = []
    for vec_id, exp_verdict in EXPECTED_VECTOR_VERDICTS.items():
        pat = re.compile(
            rf"^VECTOR\|ID={re.escape(vec_id)}\|EXPECTED=([^|]+)\|ACTUAL=([^|]+)\|MATCH=(true|false)\|DETAIL=(.+)$",
            re.M,
        )
        m = pat.search(stdout_text)
        if not m:
            errors.append(f"Missing structured VECTOR row for {vec_id}")
            continue
        exp_col, act_col, match_col, _ = m.groups()
        if exp_col != exp_verdict or act_col != exp_verdict or match_col != "true":
            errors.append(
                f"Vector {vec_id} mismatch: expected={exp_verdict}, got EXPECTED={exp_col}, ACTUAL={act_col}, MATCH={match_col}"
            )

    if "EXTRA|ID=TC-01-AFFINE-GATE|AFFINE_ACCEPTED=true|NONLINEAR_TB02_REJECTED=true" not in stdout_text:
        errors.append("Missing or failed EXTRA|ID=TC-01-AFFINE-GATE verification line")
    if "EXTRA|ID=TC-02-H1-QUOTIENT|COCYCLE_CLASS_NONZERO=true|COBOUNDARY_ANNIHILATED=true" not in stdout_text:
        errors.append("Missing or failed EXTRA|ID=TC-02-H1-QUOTIENT verification line")
    if "ALL STAGE C CELLULAR SHEAF & COHOMOLOGY VECTORS MATCH EXPECTED: true" not in stdout_text:
        errors.append("Missing final Stage C TRUE banner")

    return (len(errors) == 0, errors)


def verify_axiom_output_and_tokens(stdout_text: str, work_dir: str) -> tuple[bool, list[str]]:
    errors = []
    for bad in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if bad in stdout_text:
            errors.append(f"Forbidden axiom token detected: {bad}")

    forbidden_pat = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|partial|implemented_by|extern)\b")
    for rel in EXPECTED_FILE_PINS:
        if not rel.endswith(".lean"):
            continue
        p = os.path.join(work_dir, *rel.split("/"))
        with open(p, "r", encoding="utf-8") as f:
            stripped = strip_lean_comments(f.read())
        for m in forbidden_pat.finditer(stripped):
            errors.append(f"Forbidden source token `{m.group(1)}` in {rel}")

    for thm in THEOREMS_62:
        full_name = f"GrandZero.StageC.{thm}"
        pat_some = re.compile(rf"^'{re.escape(full_name)}' depends on axioms: \[(.*?)\]", re.M | re.S)
        pat_none = re.compile(rf"^'{re.escape(full_name)}' does not depend on any axioms$", re.M)
        m_some = pat_some.search(stdout_text)
        m_none = pat_none.search(stdout_text)
        if m_none:
            continue
        if not m_some:
            errors.append(f"Missing `#print axioms` output line for {full_name}")
            continue
        axs = [a.strip() for a in m_some.group(1).replace("\n", " ").split(",") if a.strip()]
        illegal = [a for a in axs if a not in ALLOWED_AXIOMS]
        if illegal:
            errors.append(f"Unexpected axiom(s) on {full_name}: {illegal}")
    return (len(errors) == 0, errors)


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    zip_path = os.path.join(here, ARCHIVE_NAME)
    receipt_path = os.path.join(here, "STAGE_C_EXTERNAL_REPLAY_RECEIPT.md")
    utc_now = datetime.datetime.now(datetime.timezone.utc).isoformat()

    gh_repo = os.environ.get("GITHUB_REPOSITORY", "LOCAL_OR_NON_GH_HOST")
    gh_run_id = os.environ.get("GITHUB_RUN_ID", "N/A")
    gh_run_num = os.environ.get("GITHUB_RUN_NUMBER", "N/A")
    gh_sha = os.environ.get("GITHUB_SHA", "N/A")
    gh_actor = os.environ.get("GITHUB_ACTOR", "N/A")
    os_pretty = read_os_release()

    if not os.path.isfile(zip_path):
        print(f"FATAL: Missing {ARCHIVE_NAME} in {here}", file=sys.stderr)
        return 2

    actual_zip_size = os.path.getsize(zip_path)
    actual_zip_sha = sha256_file(zip_path)
    if actual_zip_size != EXPECTED_ARCHIVE_SIZE or actual_zip_sha != EXPECTED_ARCHIVE_SHA256:
        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage C External Independent Replay Receipt (ABORTED)`\n\n")
            out.write("- **Verdict**: **`FAIL (ARCHIVE_HASH_OR_SIZE_MISMATCH)`**\n")
            out.write(f"- **Expected**: `{EXPECTED_ARCHIVE_SIZE}` B / `{EXPECTED_ARCHIVE_SHA256}`\n")
            out.write(f"- **Actual**: `{actual_zip_size}` B / `{actual_zip_sha}`\n")
        print("FATAL: Archive SHA-256 or byte size mismatch. Aborting before extraction.", file=sys.stderr)
        return 2

    lean_bin = find_bin("lean")
    lake_bin = find_bin("lake")

    with tempfile.TemporaryDirectory(prefix="gz_stage_c_ext_") as tmp_root:
        work_dir = os.path.join(tmp_root, "stage_c")
        os.makedirs(work_dir, exist_ok=True)

        extracted_names = safe_extract_zip(zip_path, work_dir)
        has_dot_lake_pre = os.path.exists(os.path.join(work_dir, ".lake"))
        exact_file_set = (extracted_names == sorted(EXPECTED_FILE_PINS.keys()))

        pin_rows = []
        pre_pins_ok = exact_file_set and (not has_dot_lake_pre)
        for rel, exp_sha in sorted(EXPECTED_FILE_PINS.items()):
            p = os.path.join(work_dir, *rel.split("/"))
            act_sha = sha256_file(p) if os.path.isfile(p) else "MISSING"
            ok = (act_sha == exp_sha)
            if not ok:
                pre_pins_ok = False
            pin_rows.append((rel, exp_sha, act_sha, ok))

        stage_a_lineage_ok = all(
            sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
            for rel, exp_sha in STAGE_A_FROZEN_LIB_PINS.items()
        )
        stage_b_lineage_ok = all(
            sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
            for rel, exp_sha in STAGE_B_FROZEN_LIB_PINS.items()
        )

        if not (pre_pins_ok and stage_a_lineage_ok and stage_b_lineage_ok):
            with open(receipt_path, "w", encoding="utf-8") as out:
                out.write("# `GRANDZERO Ω — Stage C External Independent Replay Receipt (ABORTED)`\n\n")
                out.write("- **Verdict**: **`FAIL (INTERNAL_SOURCE_PIN_OR_LINEAGE_MISMATCH)`**\n")
            print("FATAL: Internal file SHA-256 mismatch. Aborting before build.", file=sys.stderr)
            return 2

        lean_ver = subprocess.run([lean_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        lake_ver = subprocess.run([lake_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        exact_4331 = (
            lean_ver.returncode == 0
            and EXPECTED_LEAN_VERSION_SUBSTR in lean_ver.stdout
            and EXPECTED_LEAN_COMMIT in lean_ver.stdout
        )

        build_res = subprocess.run([lake_bin, "build"], cwd=work_dir, capture_output=True, text=True)
        clean_build_pass = (
            build_res.returncode == 0
            and "warning:" not in (build_res.stdout + build_res.stderr).lower()
        )

        exe_res = subprocess.run([lake_bin, "exe", "stage_c_audit"], cwd=work_dir, capture_output=True, text=True)
        vec_rows_ok, vec_errors = verify_structured_vectors(exe_res.stdout)
        audit_vectors_pass = (exe_res.returncode == 0 and vec_rows_ok)

        inspect_lean = os.path.join(tmp_root, "ext_inspect_frozen_stage_c.lean")
        with open(inspect_lean, "w", encoding="utf-8") as f:
            f.write("import StageC\n\n")
            for thm in THEOREMS_62:
                f.write(f"#check @GrandZero.StageC.{thm}\n")
                f.write(f"#print axioms GrandZero.StageC.{thm}\n")

        inspect_res = subprocess.run(
            [lake_bin, "env", "lean", inspect_lean],
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
        axiom_whitelist_ok, axiom_errors = verify_axiom_output_and_tokens(inspect_res.stdout, work_dir)
        axiom_audit_pass = (
            inspect_res.returncode == 0
            and inspect_res.stderr.strip() == ""
            and axiom_whitelist_ok
        )

        source_identity_pass = (
            sha256_file(zip_path) == EXPECTED_ARCHIVE_SHA256
            and all(
                sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
                for rel, exp_sha in EXPECTED_FILE_PINS.items()
            )
        )

        external_replay_pass = (
            pre_pins_ok
            and stage_a_lineage_ok
            and stage_b_lineage_ok
            and exact_4331
            and clean_build_pass
            and audit_vectors_pass
            and axiom_audit_pass
            and source_identity_pass
        )

        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage C External Independent Replay Receipt`\n\n")
            out.write("## 0. Environment & Run Provenance\n")
            out.write(f"- **UTC Timestamp**: `{utc_now}`\n")
            out.write(f"- **OS Release**: `{os_pretty}`\n")
            out.write(f"- **Kernel / Platform**: `{platform.platform()}` (`{platform.machine()}`)\n")
            out.write(f"- **Python Version**: `{platform.python_version()}`\n")
            out.write(f"- **GitHub Repository / Actor**: `{gh_repo}` / `{gh_actor}`\n")
            out.write(f"- **GitHub Workflow Run ID / Number / Commit**: `{gh_run_id}` / `{gh_run_num}` / `{gh_sha}`\n")
            out.write(f"- **Lean Version**: `{lean_ver.stdout.strip()}`\n")
            out.write(f"- **Lake Version**: `{lake_ver.stdout.strip().splitlines()[0] if lake_ver.stdout.strip() else ''}`\n\n")

            out.write("## 1. Eight-Boolean Conjunction Verdict Summary\n")
            out.write(f"1. `pre_pins_ok` (ZIP `{actual_zip_size}` B + `22/22` pre-build pins + no `.lake`): **`{pre_pins_ok}`**\n")
            out.write(f"2. `stage_a_lineage_ok` (`6/6` vendored `StageA` files match Stage A Final Closure SHA-256s): **`{stage_a_lineage_ok}`**\n")
            out.write(f"3. `stage_b_lineage_ok` (`6/6` vendored `StageB` files match Stage B Final Closure SHA-256s): **`{stage_b_lineage_ok}`**\n")
            out.write(f"4. `exact_4331` (`4.33.1` & commit `{EXPECTED_LEAN_COMMIT[:12]}`): **`{exact_4331}`**\n")
            out.write(f"5. `clean_build_pass` (`lake build` exit `{build_res.returncode}`, 0 warnings): **`{clean_build_pass}`**\n")
            out.write(f"6. `audit_vectors_pass` (`stage_c_audit` exit `{exe_res.returncode}` + field-level `TC-01..07b` & `EXTRA` rows): **`{audit_vectors_pass}`**\n")
            if vec_errors:
                out.write(f"   - Vector errors: `{vec_errors}`\n")
            out.write(f"7. `axiom_audit_pass` (`62/62` Stage C theorems, exit `{inspect_res.returncode}`, allowed axioms only, 0 forbidden tokens): **`{axiom_audit_pass}`**\n")
            if axiom_errors:
                out.write(f"   - Axiom errors: `{axiom_errors}`\n")
            out.write(f"8. `source_identity_pass` (post-build `22/22` source + ZIP SHA-256 unchanged): **`{source_identity_pass}`**\n")
            out.write(f"- **`ExternalReplayPass` (8-Boolean Conjunction)**: **`{'PASS' if external_replay_pass else 'FAIL'}`**\n\n")

            out.write("## 2. 22/22 Internal File SHA-256 Verification Table\n\n")
            out.write("| File | Expected SHA-256 | Actual SHA-256 | Match |\n| :--- | :--- | :--- | :---: |\n")
            for rel, exp_s, act_s, ok in pin_rows:
                out.write(f"| `{rel}` | `{exp_s}` | `{act_s}` | `{ok}` |\n")

            out.write("\n## 3. Raw `lake build` Log\n```text\n")
            out.write(build_res.stdout + build_res.stderr)
            out.write("\n```\n\n## 4. Raw `lake exe stage_c_audit` Structured Output\n```text\n")
            out.write(exe_res.stdout + exe_res.stderr)
            out.write("\n```\n\n## 5. Raw `#check` & `#print axioms` Output (All 62 `GrandZero.StageC` Theorems)\n```text\n")
            out.write(inspect_res.stdout + inspect_res.stderr)
            out.write("\n```\n")

        print(f"RECEIPT_WRITTEN: {receipt_path}")
        print(f"EXTERNAL_REPLAY_PASS: {external_replay_pass}")
        return 0 if external_replay_pass else 1


if __name__ == "__main__":
    sys.exit(main())
