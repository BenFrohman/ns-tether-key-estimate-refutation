# Kernel certificate: ns-tether-key-estimate-refutation

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/ns-tether-key-estimate-refutation |
| Certified commit | `fafda8ee708381116de864d062e479d9692c69d2` (branch `fix/textbook-notation-20261116`) |
| Lean sources | `.lean`, lakefile, manifest and toolchain files exactly as at the certified commit; the commit that adds this certificate changes only files under `lean/certificates/` |
| lake | Lake version 5.0.0-src+ba2cbbf (Lean version 4.22.0) |
| elan | installed in CI by `elan-init.sh` from leanprover/elan (master), toolchain taken from `lean-toolchain`; the workflow does not print the elan version |
| lake-manifest.json sha256 | `2dcd77f771f6f5080b5b4b83db2f22f66071c37baaf044afbcf9b3b78d305672` |
| lean-toolchain | `leanprover/lean4:v4.22.0` |
| Lean | Lean (version 4.22.0, x86_64-unknown-linux-gnu, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05, Release) |
| Mathlib | `79e94a093aff4a60fb1b1f92d9681e407124c2ca` (lake-manifest.json; inputRev `v4.22.0`) |
| Date (UTC) | 2026-11-17T06:49:55Z |
| CI run | https://github.com/BenFrohman/ns-tether-key-estimate-refutation/actions/runs/44034087402 |
| `lake build` | `Build completed successfully.` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 52 theorems in 2 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 2 of 2 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 2 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (52 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: lean4checker tag v4.22.0 (0531c5e62c6bbc21af6c8b4adc2a16d201bf8b65), Main.lean prefix match -> exact match. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

Full `#print axioms` output (verbatim from `axioms.txt`):

```
'FrohmanianTetherDraftAudit.abs_tanh_lt_one' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.arnold_part_antisymm' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.conditional_extension' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.conditional_no_finite_blowup' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.draftRiccati_implies_BKMIntegralBounded' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.draftRiccati_tether_iff_classical' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.generator_eq_classical' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.generator_indep_kappa' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.hasDerivAt_tanh' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.isTetherFlow_iff' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.observable_deriv_indep_kappa' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.projPerp_self' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.riccati_bound_nonneg' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.riccati_comparison' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.riccati_comparison_global' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.riccati_integral_bound' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tanh_cannot_match_large_data' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tanh_initial_le' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tanh_initial_lt' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tanh_solves_riccati' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tether2Form_diag_ne_zero' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tether2Form_not_antisymm' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB_degenerate_H' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB_diag_ne_zero' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB_not_antisymm' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB_not_antisymm_R2' depends on axioms: [propext, Quot.sound, Classical.choice]
'FrohmanianTetherDraftAudit.tetherB_symm' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.amplitude_exists' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.diniRiccati_false_of_touch' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.div_free' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.draftRiccati_false_of_touch' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.dx.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.dy.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.dz.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.lap.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.localized_family_violation' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.omega_at_origin' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.omega_norm_bound' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.omega_sq_le' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.rhs.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.rhs_origin' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.rightDeriv_le_of_touch' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.u₁.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.u₂.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.u₃.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₁.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₁_eq' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₂.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₂_eq' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₃.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice]
'KeyEstimate.ω₃_eq' depends on axioms: [propext, Quot.sound, Classical.choice]
```

## Rebuild

```
git clone https://github.com/BenFrohman/ns-tether-key-estimate-refutation.git && cd ns-tether-key-estimate-refutation && git checkout fafda8ee708381116de864d062e479d9692c69d2 && cd lean && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
