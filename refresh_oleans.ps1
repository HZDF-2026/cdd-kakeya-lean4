# refresh_oleans.ps1 - recompile changed modules and refresh their .olean caches (2026-08-30)
# Context: verify_build.ps1 elaborates each module from source, but imports resolve
#          against .lake oleans. After the V7 v9 recalc edited RatVerification/RealPhysics/
#          T2_Validation/DataProvenance sources, the cached RatVerification.olean still held
#          z_ocean_V7 = 41/10, so RealPhysics.z_V7_cast (cast 41/10 = 459/100) failed.
# Fix: recompile changed modules in dependency order with -R (module name) and -o (olean path).
# Usage: powershell -ExecutionPolicy Bypass -File H:\cdd_lean4\refresh_oleans.ps1
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
$buildLib = 'H:\cdd_lean4\.lake\build\lib\lean'
# dependency order: RatVerification -> RealPhysics; T2_ReactiveFluid imports Utils only;
# T2_Validation/DataProvenance import nothing (core-only); T4 imports T3_ECSChannels
# (T3 olean cached, not edited this round); root imports all
# [2026-08-30 C1/C3] added T2_ReactiveFluid (d_SC/ζ decoupling edits)
# [2026-08-31 D1] added T4_ClaimLadder: its olean was previously only refreshed
#   implicitly via root import, so a stale cached T4.olean could go unnoticed.
#   Same latent risk applies to W1/W2/W3 (root-imported, Mathlib-only deps),
#   so they are refreshed explicitly too — the full root import set is covered.
# [2026-08-31 S14] added W4_SeedPath (imports W3_DoseLandscape; root-imported)
# [2026-09-01 阶段 2e] added RH_WeilFormula (imports RH_ExplicitFormula + RH_SpectralMeasure)
# [2026-09-03 S18] added W8_FastPath (imports W2_MeasureEMA; root-imported)
# [2026-09-04 Phase 0] added W9_SpectralWeight (Mathlib-only deps; root-imported)
$mods = @('RatVerification', 'RealPhysics', 'T2_ReactiveFluid',
          'T2_Validation', 'DataProvenance', 'T4_ClaimLadder',
          'W1_WaveMedium', 'W2_MeasureEMA', 'W3_DoseLandscape',
          'W4_SeedPath', 'W8_FastPath', 'RH_WeilFormula',
          'W9_SpectralWeight', 'CddFormalization')
$fail = 0
foreach ($m in $mods) {
    if ($m -eq 'CddFormalization') {
        $out = lean -R H:\cdd_lean4 'CddFormalization.lean' -o "$buildLib\CddFormalization.olean" 2>&1
    } else {
        $out = lean -R H:\cdd_lean4 "CddFormalization\$m.lean" -o "$buildLib\CddFormalization\$m.olean" 2>&1
    }
    $errs = @($out | Where-Object { $_ -match ': error' })
    if ($LASTEXITCODE -ne 0 -or $errs.Count -gt 0) { $fail++ }
    '{0,-22} exit={1} errors={2}' -f $m, $LASTEXITCODE, $errs.Count
    if ($errs) { $errs | Select-Object -First 6 | ForEach-Object { "    $_" } }
}
if ($fail -eq 0) { "RESULT: $($mods.Count) oleans refreshed clean ($($mods.Count - 1) modules + root)" }
else { "RESULT: $fail module(s) failed" }
exit $fail
