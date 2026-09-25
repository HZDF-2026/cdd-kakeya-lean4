# compile_one.ps1 - compile a single .lean file with project LEAN_PATH
# Usage: powershell -ExecutionPolicy Bypass -File H:\cdd_lean4\compile_one.ps1 <file.lean>
param([Parameter(Mandatory=$true)][string]$File)
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
$out = lean $File 2>&1
$errs = @($out | Where-Object { "$_" -match ': error' })
$warns = @($out | Where-Object { "$_" -match ': warning' })
$sorries = @($out | Where-Object { "$_" -match "uses 'sorry'" })
'exit={0} errors={1} warnings={2} sorry={3}' -f $LASTEXITCODE, $errs.Count, $warns.Count, $sorries.Count
if ($errs) { $errs | ForEach-Object { "E: $_" } }
if ($warns) { $warns | ForEach-Object { "W: $_" } }
if ($sorries) { $sorries | ForEach-Object { "S: $_" } }
exit $errs.Count
