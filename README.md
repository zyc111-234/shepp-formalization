# Shepp criterion: single-file Lean verification

The Lean formalization supporting the paper-facing results listed below is
contained in [`formal/Shepp.lean`](formal/Shepp.lean). The file has a single
direct import, `Mathlib`. The project pins both Lean and Mathlib to
`v4.33.0-rc1`.

## Verification

Install [elan](https://github.com/leanprover/elan), then run in PowerShell:

```powershell
cd formal
.\verify.ps1
```

The script scans the source for proof placeholders and project-level axiom
declarations, downloads the pinned Mathlib cache, builds `Shepp.lean`, and
checks the transitive axioms of the paper-facing declarations listed below.

A successful run ends with:

```text
Verification passed: Shepp.lean compiled and all public endpoints use only standard axioms.
```

The portable core build commands are:

```text
cd formal
lake exe cache get
lake build Shepp
```

These core commands build the formalization. Run `verify.ps1` for the additional
source scan and paper-facing axiom audit.

GitHub Actions repeats the verification on both `ubuntu-latest` and
`windows-latest` and additionally audits the complete `Shepp` namespace.

## Paper-facing declarations

| Mathematical result | Lean declaration |
|---|---|
| Shared-noise resistance bound | `Shepp.Section4.paperSharedNoiseResistance_bound` |
| Shared-noise extinction criterion | `Shepp.Section4.paperSharedNonextinction_tendsto_zero` |
| Spatial finite-time extinction | `Shepp.Section5.spatialResidual_finiteTimeExtinction` |
| Main Shepp criterion | `Shepp.Section8.mainCriterion` |
| Explicit relabelled radius-sequence criterion | `Shepp.Section8.exists_relabelledExplicitRadiusSequenceCriterion` |

For every declaration in the table, `Lean.collectAxioms` returns exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
