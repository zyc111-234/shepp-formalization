$ErrorActionPreference = "Stop"

$ProjectDirectory = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProofFile = Join-Path $ProjectDirectory "Shepp.lean"
$LakeExecutable = "lake"

$Source = Get-Content -LiteralPath $ProofFile -Raw -Encoding UTF8
$ForbiddenPatterns = @(
  "\b(?:sorryAx|sorry|admit)\b",
  "(?m)^\s*(?:axiom|axioms|constant|constants|postulate|postulates|opaque)\b",
  "(?m)^\s*set_option\s+debug\.skipKernelTC\s+true\b",
  "(?m)^\s*unsafe\s+(?:def|theorem|lemma|instance|structure|inductive)\b"
)
foreach ($Pattern in $ForbiddenPatterns) {
  if ([regex]::IsMatch($Source, $Pattern)) {
    throw "Forbidden proof construct matched: $Pattern"
  }
}

Push-Location -LiteralPath $ProjectDirectory
try {
  & $LakeExecutable exe cache get
  if ($LASTEXITCODE -ne 0) { throw "Mathlib cache download failed." }

  & $LakeExecutable build Shepp
  if ($LASTEXITCODE -ne 0) { throw "Lean kernel build failed." }

  $AuditDirectory = Join-Path $ProjectDirectory ".lake"
  $AuditFile = Join-Path $AuditDirectory "SheppAxiomAudit.lean"
  $AuditSource = @'
import Shepp

open Lean Meta Elab Command

elab "assert_standard_axioms " declaration:ident : command => do
  let declarationName := declaration.getId
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms declarationName
  let unexpected := axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "{declarationName} uses unexpected axioms: {unexpected}"
  logInfo m!"{declarationName}: {axioms}"

assert_standard_axioms Shepp.Section4.paperSharedNoiseResistance_bound
assert_standard_axioms Shepp.Section4.paperSharedNonextinction_tendsto_zero
assert_standard_axioms Shepp.Section5.spatialResidual_finiteTimeExtinction
assert_standard_axioms Shepp.Section8.mainCriterion
assert_standard_axioms Shepp.Section8.exists_relabelledExplicitRadiusSequenceCriterion
'@
  [System.IO.File]::WriteAllText($AuditFile, $AuditSource,
    [System.Text.UTF8Encoding]::new($false))
  try {
    & $LakeExecutable env lean $AuditFile
    if ($LASTEXITCODE -ne 0) { throw "Transitive axiom audit failed." }
  } finally {
    if (Test-Path -LiteralPath $AuditFile) {
      Remove-Item -LiteralPath $AuditFile -Force
    }
  }
} finally {
  Pop-Location
}

Write-Output "Verification passed: Shepp.lean compiled and all public endpoints use only standard axioms."
