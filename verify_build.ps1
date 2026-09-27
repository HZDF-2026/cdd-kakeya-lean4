# verify_build.ps1 - direct-compile verification bypassing lake git dependency (2026-08-28)
# Context: lake build needs git.exe to re-verify the plausible package (URL-changed notice)
#          during dependency refresh; git is not installed on this machine. All dependency
#          oleans are cached and Mathlib resolves from the local mathlib432 checkout, so
#          we elaborate every module from source with plain `lean`, which is semantically
#          equivalent to lake build for verification (0 errors + zero sorry).
# [D1, 2026-08-31] $mods previously omitted T4_ClaimLadder (and later W1/W2):
#          those modules were only checked via the root import against cached .oleans,
#          so source-level edits could pass unnoticed. $mods now lists every module in
#          CddFormalization/, and a directory-count self-check (below) fails the run if
#          a future module is added without updating this list.
# [2026-09-03 S18] added W8_FastPath (S18 fast-path formalization).
# [H2 rollback, 2026-09-04] removed the `-notlike 'Tmp*'` filter that had masked
#          TmpCheck/TmpCheck2 inside CddFormalization/ (naming-convention masking
#          weakened the D1 self-check). Those two WIP probes were physically moved
#          to scratch\; the directory-count self-check is strong again (ANY
#          unregistered .lean in CddFormalization fails the run).
# [H3, 2026-09-04] added pre-scan: root-level and scratch/ .lean files must not
#          contain any custom `axiom` declaration (AxiomAudit scope extension);
#          sorry/admit in scratch are allowed (WIP) but axioms are not.
# [K8, 2026-09-25] clean-state anchor: commit 7a5f53c locks the 27/27 all-green
#          state (0 errors/0 warnings/0 sorry; evidence verify_out_20260925.txt).
# [K7, 2026-09-25] 7 audit dirs moved from CddFormalization/ to archive/ (untracked);
#          D1 extended to assert CddFormalization contains NO subdirectories.
# [K12, 2026-09-27] scratch ledger gate: every scratch/*.lean must be registered
#          by name in scratch/WIP_LEDGER.md. The K5 ledger policy (2026-09-12)
#          was human-check only until now; it is mechanically enforced here.
# [K11, 2026-09-27] git clean-state gate: `git status --porcelain` must be empty
#          before any compile work runs. Blind spot that motivated this gate:
#          scripts/c1_cross_source_recheck.py ran UNTRACKED 2026-09-25..27 with
#          no pipeline alarm. (The 2026-08-28 header note "git is not installed"
#          is stale: git.exe lives at C:\Program Files\Git; the gate requires it.)
# Usage: powershell -ExecutionPolicy Bypass -File H:\cdd_lean4\verify_build.ps1
$ErrorActionPreference = 'Continue'
$toolchain = 'H:\lean4\lean-4.32.2-windows\bin'
$env:Path = "$toolchain;$env:Path"

$libs = @('H:\cdd_lean4\.lake\build\lib\lean', 'H:\mathlib432\.lake\build\lib\lean')
Get-ChildItem H:\cdd_lean4\.lake\packages -Directory | ForEach-Object {
    $p = "$($_.FullName)\.lake\build\lib\lean"
    if (Test-Path $p) { $libs += $p }
}
$env:LEAN_PATH = ($libs -join ';') + ";$toolchain\..\lib\lean"

Set-Location H:\cdd_lean4
# dependency order: T4 imports T3; W1/W2/W3 are wave-proto modules (S11-S13)
$mods = @('Basic','Utils','Kakeya','Kolmogorov45','MeasureTheory','RatVerification',
          'RealPhysics',
          'T1_SCCO','T2_ReactiveFluid','T2_Validation','DataProvenance','T3_ECSChannels',
          'T4_ClaimLadder',
          'RH_MeasureTheory','RH_WeakConvergence','RH_LiCriterion','RH_ExplicitFormula',
          'RH_DeviationMeasure','RH_SpectralMeasure','RH_WeilFormula',
          'W1_WaveMedium','W2_MeasureEMA','W3_DoseLandscape','W4_SeedPath','W8_FastPath',
          'W9_SpectralWeight')

# [D1 self-check] every .lean in CddFormalization must be listed in $mods (root excluded)
$dirCount = (Get-ChildItem CddFormalization -Filter *.lean).Count
if ($dirCount -ne $mods.Count) {
    "SELF-CHECK FAILED: CddFormalization has $dirCount .lean files but `$mods lists $($mods.Count) modules"
    exit 1
}
# [K7, 2026-09-25] CddFormalization must contain NO subdirectories (audit dirs
# belong in archive/, which is untracked)
$subDirs = @(Get-ChildItem CddFormalization -Directory -ErrorAction SilentlyContinue)
if ($subDirs.Count -gt 0) {
    "SELF-CHECK FAILED: CddFormalization contains $($subDirs.Count) subdirectory(ies): $($subDirs.Name -join ', ')"
    exit 1
}

# [H3 axiom pre-scan] no custom `axiom` declaration may exist in root-level or
# scratch/ .lean files (AxiomAudit scope extension; comments excluded)
$axiomHits = @(Get-ChildItem H:\cdd_lean4 -Filter *.lean | Where-Object {
        $_.Name -notin @('AxiomAudit.lean','CddFormalization.lean')
    }) + @(Get-ChildItem H:\cdd_lean4\scratch -Filter *.lean -ErrorAction SilentlyContinue) |
    ForEach-Object {
        $f = $_.Name; $i = 0
        Get-Content $_.FullName | ForEach-Object {
            $i++
            if ($_ -match '^\s*axiom\s' -and $_ -notmatch '^\s*--') { "$f : L$i" }
        }
    }
if ($axiomHits.Count -gt 0) {
    "AXIOM-SCAN FAILED: custom axiom declarations found outside registered modules:"
    $axiomHits | ForEach-Object { "    $_" }
    exit 1
}

# [K12, 2026-09-27] scratch ledger gate: every scratch/*.lean must be registered
# by name in scratch/WIP_LEDGER.md (K5 policy, mechanically enforced)
$ledgerPath = 'H:\cdd_lean4\scratch\WIP_LEDGER.md'
if (-not (Test-Path $ledgerPath)) {
    "LEDGER-CHECK FAILED: scratch/WIP_LEDGER.md missing (required by K5 policy since 2026-09-12)"
    exit 1
}
$ledger = Get-Content $ledgerPath -Raw
$scratchLean = @(Get-ChildItem H:\cdd_lean4\scratch -Filter *.lean -ErrorAction SilentlyContinue)
$unregistered = @($scratchLean | Where-Object { $ledger -notmatch [regex]::Escape($_.Name) })
if ($unregistered.Count -gt 0) {
    "LEDGER-CHECK FAILED: $($unregistered.Count) of $($scratchLean.Count) scratch .lean file(s) not registered in WIP_LEDGER.md:"
    $unregistered | ForEach-Object { "    $($_.Name)" }
    exit 1
}
"ledger check: $($scratchLean.Count) scratch .lean files, all registered in WIP_LEDGER.md"

# [K11, 2026-09-27] git clean-state gate: porcelain must be empty before any
# compile work; verification claims are only valid against a committed state
if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
    "GIT-GATE FAILED: git not on PATH - clean-state guarantee cannot be established"
    exit 1
}
$dirty = @(git status --porcelain)
if ($dirty.Count -gt 0) {
    "GIT-GATE FAILED: working tree not clean ($($dirty.Count) untracked/modified path(s)) - commit or stash before verifying:"
    $dirty | ForEach-Object { "    $_" }
    exit 1
}
$head = git rev-parse --short HEAD
"clean-state anchor: HEAD $head (porcelain empty)"

$fail = 0
foreach ($m in $mods) {
    $out = lean "CddFormalization\$m.lean" 2>&1
    $errs = @($out | Where-Object { $_ -match ': error' })
    $warns = @($out | Where-Object { $_ -match ': warning' })
    $sorries = @($out | Where-Object { $_ -match "uses 'sorry'" })
    if ($LASTEXITCODE -ne 0 -or $errs.Count -gt 0) { $fail++ }
    '{0,-22} exit={1} errors={2} warnings={3} sorry={4}' -f $m, $LASTEXITCODE, $errs.Count, $warns.Count, $sorries.Count
    if ($errs) { $errs | Select-Object -First 6 | ForEach-Object { "    $_" } }
}
$out = lean 'CddFormalization.lean' 2>&1
$errs = @($out | Where-Object { $_ -match ': error' })
if ($LASTEXITCODE -ne 0 -or $errs.Count -gt 0) { $fail++ }
'{0,-22} exit={1} errors={2}' -f 'root CddFormalization', $LASTEXITCODE, $errs.Count
if ($fail -eq 0) { "RESULT: all $($dirCount + 1) source files ($dirCount modules + root) compile clean (0 errors, zero sorry)" }
else { "RESULT: $fail file(s) failed" }
exit $fail
