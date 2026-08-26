# Shepp criterion: single-file Lean verification

The complete formal proof is [`formal/Shepp.lean`](formal/Shepp.lean). It has
one external import, Mathlib, pinned to `v4.33.0-rc1` together with Lean
`v4.33.0-rc1`.

## Verify

Install [elan](https://github.com/leanprover/elan), then run in PowerShell:

```powershell
cd formal
.\verify.ps1
```

The script downloads the pinned Mathlib cache, builds `Shepp.lean`, rejects
proof placeholders and project axioms, and checks the transitive axioms of the
paper-facing declarations. A successful run ends with:

```text
Verification passed: Shepp.lean compiled and all public endpoints use only standard axioms.
```

The portable core build commands are:

```text
lake exe cache get
lake build Shepp
```

## Paper-facing declarations

| Mathematical result | Lean declaration |
|---|---|
| Shared-noise resistance bound | `Shepp.Section4.paperSharedNoiseResistance_bound` |
| Shared-noise extinction criterion | `Shepp.Section4.paperSharedNonextinction_tendsto_zero` |
| Spatial finite-time extinction | `Shepp.Section5.spatialResidual_finiteTimeExtinction` |
| Main Shepp criterion | `Shepp.Section8.mainCriterion` |
| Explicit relabelled radius-sequence criterion | `Shepp.Section8.exists_relabelledExplicitRadiusSequenceCriterion` |

For every declaration in the table, Lean reports exactly the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.
