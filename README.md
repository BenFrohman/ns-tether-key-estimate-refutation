# The Riccati vorticity estimate M′ ≤ C − kM² fails for 3D Navier–Stokes on T³

**An explicit counterexample and a Lean-checked audit of the symplectic-tether draft**

Benjamin Stanley Frohman · Independent Researcher, Texas, United States ·
ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)

Paper: [`paper/ns-key-estimate-refutation.pdf`](paper/ns-key-estimate-refutation.pdf) ·
Code license: Apache-2.0 · Paper license: CC BY 4.0

> **Scope.** This repository does **not** prove or disprove global regularity of the 3D Navier–Stokes
> equations, and it makes **no claim about the Clay Millennium Problem**. It shows that one specific
> estimate, used in an earlier unpublished draft of mine, is false in the form that draft used.

## In plain English

My earlier draft argued that the largest vorticity in a 3D viscous fluid, M(t), always obeys
M′ ≤ C − k·M². If that were true, M could never run away, and the Navier–Stokes equations would never
blow up. This repository checks that claim.

### What is refuted (shown false)

- **The draft's version (C, k depend only on the viscosity ν): false.**
  The counterexample is the explicit starting flow u₀ = A·U, with
  U = 3(−sin y, sin x, 0) + (−sin x cos z, 0, cos x sin z).
  - Its vorticity is ω = A·(0, 2 sin x sin z, 3(cos x + cos y)).
  - The vorticity is largest at the origin, where M(0) = 6A.
  - At the origin, vortex stretching adds 6A² and viscosity removes 6νA. So M starts out *growing* at
    a rate of at least 6A(A − ν).
  - The estimate demands that M start *shrinking* once M is large. For any fixed C and k, the choice
    A = ν + 1 + |C|/k breaks it.
- **Constants allowed to depend on ν and the fluid's energy, in any way: also false.** The
  counterexample here is a small, intense vortex. Shrinking it makes the peak vorticity grow like λ²
  and its growth rate grow like λ⁴, while a background flow keeps the energy fixed. The same family
  also refutes constants that depend on ν and ‖u₀‖_{L³}.
- **The draft's "symplectic tether" (checked in Lean):**
  - The tether form is symmetric, not antisymmetric, so it is not symplectic.
  - Because the tether vanishes against the energy (B(F,H) = 0), it never changes the flow. Any
    vorticity control would have to hold for plain Navier–Stokes, so it cannot come from the tether.
  - The draft's tanh solution formula can never match starting data above √(C/k).

### What is proved

- The scalar and calculus steps of both counterexamples are proved in Lean.
- The "touching" lemma that turns them into violations is proved in Lean.
- The conditional chain is proved in Lean: *if* the Riccati estimate held, then together with the
  Beale–Kato–Majda criterion there would be no finite-time blow-up. Both the estimate and BKM appear as
  explicit hypotheses, not hidden assumptions.

### What is still open

If C and k may depend on the starting flow in an arbitrary way, the estimate is equivalent to global
regularity itself. That version is **open**, and nothing here settles it.

### What is in Lean and what is cited

| In Lean (machine-checked) | Cited or computed outside Lean |
|---|---|
| Touching lemma (differentiable and Dini forms) | Kato local existence and smoothness up to t = 0, which identifies g′(0) with the vorticity equation's right-hand side |
| div U = 0, curl U, \|curl U\| ≤ 6 with equality at 0, exact right-hand side (0, 0, 6A(A−ν)) at the origin | Danskin-type bound D⁺M ≤ ‖∂ₜω‖∞ (only for the V3 remark) |
| Amplitude choice; scalar step of the localized family | Beale–Kato–Majda criterion (a hypothesis in Lean) |
| All tether-audit statements; conditional chain | Symbolic values of the localized vortex (sympy) and the rigorous Arb interval certificate of its maximum |
| | Decay and eventual-smallness facts used in the V3 equivalence |

Numerical simulations (`scripts/ns_check.py`) are **supporting only** and are not part of any proof.

## Verify it yourself (one command)

Requirements: [elan](https://github.com/leanprover/elan), git, curl, and python3 (3.10 or later) with venv.

```bash
git clone https://github.com/BenFrohman/ns-tether-key-estimate-refutation
cd ns-tether-key-estimate-refutation
./verify.sh              # add --numerics to also run the (supporting-only) simulation
```

`verify.sh` runs four steps:
1. It downloads the Mathlib build cache and builds both Lean files: `lake exe cache get && lake build`
   in `lean/`.
2. It prints the axioms of all 50 declarations and fails unless they use only `propext`,
   `Classical.choice` and `Quot.sound`.
3. It creates `.venv` with the pinned Python packages.
4. It re-runs the exact sympy checks and the Arb maximum certificate, and fails if any expected value
   doesn't match.

## Reproducibility

- **Source commit:** `SOURCE-COMMIT-PLACEHOLDER`. The Lean files, scripts and `verify.sh` are exactly
  those of this commit. Tag `v1.0.0` adds only the compiled PDF and these recorded hashes.
- **Lean:** 4.22.0 (`leanprover/lean4:v4.22.0`, commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`).
- **Mathlib:** `v4.22.0`, revision `79e94a093aff4a60fb1b1f92d9681e407124c2ca` (pinned in
  `lean/lake-manifest.json`).
- **Python:** 3.13.5 with python-flint 0.9.0, sympy 1.14.0, mpmath 1.3.0 and numpy 2.5.4
  (`scripts/requirements.txt`).
- **File checksums:** listed in `SHA256SUMS`.
  - `lean/FrohmanianTetherDraftAudit.lean`: SHA-256 `e8e1586595227781249e848d880ac27d527c46d6bbebdba50bedf44cdab973a5`
  - `lean/KeyEstimateRefutation.lean`: SHA-256 `2f6028585612e9a6fd0a68da0d53da5a87c7aaf49f0fcaf27617a4b20aed9545`

Output of `cd lean && lake env lean PrintAxioms.lean`, verbatim:

```
'FrohmanianTetherDraftAudit.riccati_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.riccati_comparison_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.riccati_bound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.riccati_integral_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.DraftRiccatiEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.BKMIntegralBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.BKMContinuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.draftRiccati_implies_BKMIntegralBounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FrohmanianTetherDraftAudit.conditional_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.conditional_no_finite_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.projPerp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.projPerp_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB_degenerate_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB_diag_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB_not_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherB_not_antisymm_R2' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tether2Form' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.arnold_part_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tether2Form_diag_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tether2Form_not_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tetherGenerator' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.generator_eq_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.generator_indep_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.IsTetherFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.isTetherFlow_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.observable_deriv_indep_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.draftRiccati_tether_iff_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FrohmanianTetherDraftAudit.hasDerivAt_tanh' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.abs_tanh_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tanh_solves_riccati' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tanh_initial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tanh_initial_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTetherDraftAudit.tanh_cannot_match_large_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.DraftRiccatiEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.DiniRiccatiEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.rightDeriv_le_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.draftRiccati_false_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.diniRiccati_false_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.div_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.w1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.w2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.w3_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.omega_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.omega_at_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.omega_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.rhs_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.amplitude_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KeyEstimate.localized_family_violation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Layout

- `lean/`: a single Lake project containing `FrohmanianTetherDraftAudit.lean`, `KeyEstimateRefutation.lean`
  and `PrintAxioms.lean`.
- `scripts/`:
  - `v1_trig_example.py`: exact sympy checks for V1.
  - `v2_symbolic.py`: exact values for the localized vortex.
  - `v2_maxcert.py`: the Arb interval certificate.
  - `v2_explore.py`: a grid cross-check.
  - `ns_check*.py`: the supporting-only simulations.
  - `logs/`: the original run logs.
- `paper/`: the LaTeX note and its PDF.
- `provenance/`: the original working reports and build logs, kept for the record.

## License

The code is licensed under Apache-2.0 ([LICENSE](LICENSE)). The paper and prose are licensed under
CC BY 4.0 ([LICENSE-paper](LICENSE-paper)). See [NOTICE](NOTICE) and [CITATION.cff](CITATION.cff).
