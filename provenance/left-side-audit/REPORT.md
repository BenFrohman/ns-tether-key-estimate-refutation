# REPORT — FrohmanianTetherDraftAudit.lean

Author: Benjamin Stanley Frohman · License: Apache-2.0 · © 2026
Date: 2026-11-09 (America/Chicago, CST)
Path: `/workspace/left-side-lean-2026-11-09/FrohmanianTetherDraftAudit.lean`
SHA-256: `e8e1586595227781249e848d880ac27d527c46d6bbebdba50bedf44cdab973a5`
Toolchain: Lean 4.22.0, Mathlib v4.22.0 (`79e94a093aff4a60fb1b1f92d9681e407124c2ca`); packages symlinked from the same tree as
`/workspace/triple-architecture-build-2026-11-09` (no existing files modified; no git, no push, no publish).

## Scope

This file does **not** prove global regularity of 3D Navier–Stokes. The draft's key estimate
`M' ≤ C − k M²` is the explicit open hypothesis `DraftRiccatiEstimate`; the BKM criterion is the explicit
hypothesis `BKMContinuation`. No `structure`/`class` is declared, so no fields can smuggle conclusions.

## Build

`lake build` → ✔ [7083/7084] Built FrohmanianTetherDraftAudit / Build completed successfully.  (log: `logs/lake_build.log`; also `lake env lean` clean with zero warnings, `logs/iter2.log`).

## Forbidden-token scan

`grep -nE '\b(sorry|admit|axiom|native_decide|opaque|implemented_by|unsafe|structure|class)\b'` → **0 hits** (comments included).

## `#print axioms` (every declaration; `logs/PrintAxioms.lean`, `logs/axioms.log`)

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
```

Only `propext`, `Classical.choice`, `Quot.sound`.

## Statements were not weakened

Everything requested was proved. Things deliberately *not* claimed: the converse of 2d (that every
|y₀| < √(C/k) is reached by some φ₀ — true via artanh, not needed for the refutation and not formalized); any
derivation of `DraftRiccatiEstimate` or BKM from Navier–Stokes (open / cited, respectively).
Note on 2c: `IsTetherFlow` is an abstract weak formulation (∀ observables F, d/dt F(γ t) = generator); it models the
draft's bracket-generated dynamics, not a PDE solution concept.

## Declarations (verbatim statements) and meanings

### `riccati_comparison`
M' ≤ C − kM² on [0,T) ⇒ M ≤ max(M 0, √(C/k)) on [0,T) (barrier argument, any real T).

```lean
theorem riccati_comparison {M M' : ℝ → ℝ} {C k T : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt M (M' t) t)
    (hineq : ∀ t ∈ Ico 0 T, M' t ≤ C - k * M t ^ 2) :
    ∀ t ∈ Ico 0 T, M t ≤ max (M 0) (Real.sqrt (C / k)) :=
```

### `riccati_comparison_global`
Same bound on [0,∞) (the T = ∞ case).

```lean
theorem riccati_comparison_global {M M' : ℝ → ℝ} {C k : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt M (M' t) t)
    (hineq : ∀ t ∈ Ici (0:ℝ), M' t ≤ C - k * M t ^ 2) :
    ∀ t ∈ Ici (0:ℝ), M t ≤ max (M 0) (Real.sqrt (C / k)) :=
```

### `riccati_bound_nonneg`
The bound max(M0, √(C/k)) is ≥ 0.

```lean
lemma riccati_bound_nonneg (M0 C k : ℝ) : 0 ≤ max M0 (Real.sqrt (C / k)) :=
```

### `riccati_integral_bound`
∫₀ᵗ M ≤ max(M 0, √(C/k))·t on [0,T) (finite BKM integral).

```lean
theorem riccati_integral_bound {M M' : ℝ → ℝ} {C k T : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt M (M' t) t)
    (hineq : ∀ t ∈ Ico 0 T, M' t ≤ C - k * M t ^ 2) :
    ∀ t ∈ Ico 0 T, ∫ s in (0:ℝ)..t, M s ≤ max (M 0) (Real.sqrt (C / k)) * t :=
```

### `DraftRiccatiEstimate`
OPEN hypothesis: the draft's key estimate; NOT derived from NS.

```lean
def DraftRiccatiEstimate (M M' : ℝ → ℝ) (C k T : ℝ) : Prop :=
```

### `BKMIntegralBounded`
∃ B, ∀ t∈[0,T*), ∫₀ᵗ M ≤ B.

```lean
def BKMIntegralBounded (M : ℝ → ℝ) (Tstar : ℝ) : Prop :=
```

### `BKMContinuation`
Hypothesis: bounded BKM integral on [0,T*) ⇒ Extends T*.

```lean
def BKMContinuation (M : ℝ → ℝ) (Extends : ℝ → Prop) (Tstar : ℝ) : Prop :=
```

### `draftRiccati_implies_BKMIntegralBounded`
Open estimate ⇒ bounded BKM integral.

```lean
theorem draftRiccati_implies_BKMIntegralBounded {M M' : ℝ → ℝ} {C k Tstar : ℝ}
    (hR : DraftRiccatiEstimate M M' C k Tstar) : BKMIntegralBounded M Tstar :=
```

### `conditional_extension`
Open estimate + BKM hypothesis ⇒ solution extends past T*.

```lean
theorem conditional_extension {M M' : ℝ → ℝ} {Extends : ℝ → Prop} {C k Tstar : ℝ}
    (hR : DraftRiccatiEstimate M M' C k Tstar) (hBKM : BKMContinuation M Extends Tstar) :
    Extends Tstar :=
```

### `conditional_no_finite_blowup`
Both hypotheses for every T* ⇒ extends past every finite T* (conditional only).

```lean
theorem conditional_no_finite_blowup {M M' : ℝ → ℝ} {Extends : ℝ → Prop} {C k : ℝ}
    (hR : ∀ Tstar : ℝ, DraftRiccatiEstimate M M' C k Tstar)
    (hBKM : ∀ Tstar : ℝ, BKMContinuation M Extends Tstar) :
    ∀ Tstar : ℝ, Extends Tstar :=
```

### `projPerp`
P⊥Φ = Φ − (⟨Φ,u⟩/‖u‖²)u.

```lean
def projPerp (u Φ : V) : V :=
```

### `tetherB`
B(dF,dG) = −κW⟨P⊥dF, P⊥dG⟩.

```lean
def tetherB (κ W : ℝ) (u dF dG : V) : ℝ :=
```

### `projPerp_self`
P⊥u = 0 (incl. u = 0).

```lean
lemma projPerp_self (u : V) : projPerp u u = 0 :=
```

### `tetherB_symm`
B is symmetric.

```lean
theorem tetherB_symm (κ W : ℝ) (u dF dG : V) :
    tetherB κ W u dF dG = tetherB κ W u dG dF :=
```

### `tetherB_degenerate_H`
B(F,H) = 0 when dH = u.

```lean
theorem tetherB_degenerate_H (κ W : ℝ) (u dF : V) : tetherB κ W u dF u = 0 :=
```

### `tetherB_diag_ne_zero`
κ≠0, W≠0, P⊥v≠0 ⇒ B(v,v) ≠ 0.

```lean
theorem tetherB_diag_ne_zero {κ W : ℝ} (hκ : κ ≠ 0) (hW : W ≠ 0) (u v : V)
    (hv : projPerp u v ≠ 0) : tetherB κ W u v v ≠ 0 :=
```

### `tetherB_not_antisymm`
Refutes A1/Lemma 3: B is not antisymmetric (general V).

```lean
theorem tetherB_not_antisymm {κ W : ℝ} (hκ : κ ≠ 0) (hW : W ≠ 0) (u v : V)
    (hv : projPerp u v ≠ 0) :
    ¬ ∀ dF dG : V, tetherB κ W u dF dG = -tetherB κ W u dG dF :=
```

### `tetherB_not_antisymm_R2`
Concrete witness in ℝ² with u=e₁, dF=e₂.

```lean
theorem tetherB_not_antisymm_R2 {κ W : ℝ} (hκ : κ ≠ 0) (hW : W ≠ 0) :
    tetherB κ W (EuclideanSpace.single (0 : Fin 2) (1:ℝ)) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) ≠ 0 ∧
    ¬ ∀ dF dG : EuclideanSpace ℝ (Fin 2),
      tetherB κ W (EuclideanSpace.single 0 1) dF dG
        = -tetherB κ W (EuclideanSpace.single 0 1) dG dF :=
```

### `tether2Form`
T(a,b) = ω·(a×b) − κ|ω|²(a·b) on ℝ³.

```lean
def tether2Form (κ : ℝ) (ω a b : Fin 3 → ℝ) : ℝ :=
```

### `arnold_part_antisymm`
The Arnold part ω·(a×b) alone is antisymmetric.

```lean
theorem arnold_part_antisymm (ω a b : Fin 3 → ℝ) :
    ω ⬝ᵥ (a ×₃ b) = -(ω ⬝ᵥ (b ×₃ a)) :=
```

### `tether2Form_diag_ne_zero`
T(ω,ω) ≠ 0 for κ≠0, ω≠0.

```lean
theorem tether2Form_diag_ne_zero {κ : ℝ} (hκ : κ ≠ 0) {ω : Fin 3 → ℝ} (hω : ω ≠ 0) :
    tether2Form κ ω ω ω ≠ 0 :=
```

### `tether2Form_not_antisymm`
Refutes Thm 4.1/Lemma 3: T is not a 2-form, so not symplectic.

```lean
theorem tether2Form_not_antisymm {κ : ℝ} (hκ : κ ≠ 0) {ω : Fin 3 → ℝ} (hω : ω ≠ 0) :
    ¬ ∀ a b : Fin 3 → ℝ, tether2Form κ ω a b = -tether2Form κ ω b a :=
```

### `tetherGenerator`
dF/dt = {F,H}_LP + [F,H]_diss + B(F,H), all pieces explicit arguments.

```lean
def tetherGenerator (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ) (grad : (S → ℝ) → S → V)
    (W : S → ℝ) (vel : S → V) (H : S → ℝ) (κ : ℝ) (F : S → ℝ) (ω : S) : ℝ :=
```

### `generator_eq_classical`
With δH/δω = u, the generator equals the classical one for every κ.

```lean
theorem generator_eq_classical (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ)
    (grad : (S → ℝ) → S → V) (W : S → ℝ) (vel : S → V) (H : S → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (F : S → ℝ) (ω : S) :
    tetherGenerator LP diss grad W vel H κ F ω = LP F H ω + diss F H ω :=
```

### `generator_indep_kappa`
Generator is independent of κ.

```lean
theorem generator_indep_kappa (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ)
    (grad : (S → ℝ) → S → V) (W : S → ℝ) (vel : S → V) (H : S → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ₁ κ₂ : ℝ) (F : S → ℝ) (ω : S) :
    tetherGenerator LP diss grad W vel H κ₁ F ω = tetherGenerator LP diss grad W vel H κ₂ F ω :=
```

### `IsTetherFlow`
Weak trajectory of the κ-tethered evolution.

```lean
def IsTetherFlow (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ) (grad : (S → ℝ) → S → V)
    (W : S → ℝ) (vel : S → V) (H : S → ℝ) (κ : ℝ) (γ : ℝ → S) : Prop :=
```

### `isTetherFlow_iff`
Trajectories for κ₁ and κ₂ coincide: the tether never changes the flow.

```lean
theorem isTetherFlow_iff (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ)
    (grad : (S → ℝ) → S → V) (W : S → ℝ) (vel : S → V) (H : S → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ₁ κ₂ : ℝ) (γ : ℝ → S) :
    IsTetherFlow LP diss grad W vel H κ₁ γ ↔ IsTetherFlow LP diss grad W vel H κ₂ γ :=
```

### `observable_deriv_indep_kappa`
Any observable's derivative along the flow equals its classical (κ=0) value.

```lean
theorem observable_deriv_indep_kappa (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ)
    (grad : (S → ℝ) → S → V) (W : S → ℝ) (vel : S → V) (H : S → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (γ : ℝ → S)
    (hγ : IsTetherFlow LP diss grad W vel H κ γ) (Mfun : S → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Mfun (γ s)) (tetherGenerator LP diss grad W vel H 0 Mfun (γ t)) t ∧
    HasDerivAt (fun s => Mfun (γ s)) (LP Mfun H (γ t) + diss Mfun H (γ t)) t :=
```

### `draftRiccati_tether_iff_classical`
Draft Riccati estimate for tethered flow ⇔ for classical flow: feedback can't come from the tether.

```lean
theorem draftRiccati_tether_iff_classical (LP diss : (S → ℝ) → (S → ℝ) → S → ℝ)
    (grad : (S → ℝ) → S → V) (W : S → ℝ) (vel : S → V) (H : S → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (γ : ℝ → S) (Mfun : S → ℝ) (C k T : ℝ) :
    DraftRiccatiEstimate (fun s => Mfun (γ s))
        (fun s => tetherGenerator LP diss grad W vel H κ Mfun (γ s)) C k T ↔
      DraftRiccatiEstimate (fun s => Mfun (γ s))
        (fun s => tetherGenerator LP diss grad W vel H 0 Mfun (γ s)) C k T :=
```

### `hasDerivAt_tanh`
tanh' = 1 − tanh².

```lean
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x :=
```

### `abs_tanh_lt_one`
|tanh x| < 1.

```lean
lemma abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 :=
```

### `tanh_solves_riccati`
y = √(C/k)·tanh(√(Ck)t + φ₀) solves y' = C − ky².

```lean
theorem tanh_solves_riccati {C k : ℝ} (hC : 0 ≤ C) (hk : 0 < k) (φ0 t : ℝ) :
    HasDerivAt (fun s => Real.sqrt (C / k) * Real.tanh (Real.sqrt (C * k) * s + φ0))
      (C - k * (Real.sqrt (C / k) * Real.tanh (Real.sqrt (C * k) * t + φ0)) ^ 2) t :=
```

### `tanh_initial_le`
|y(0)| ≤ √(C/k) for the tanh formula.

```lean
theorem tanh_initial_le {C k : ℝ} (φ0 : ℝ) :
    |Real.sqrt (C / k) * Real.tanh φ0| ≤ Real.sqrt (C / k) :=
```

### `tanh_initial_lt`
With C > 0, |y(0)| < √(C/k) strictly.

```lean
theorem tanh_initial_lt {C k : ℝ} (hC : 0 < C) (hk : 0 < k) (φ0 : ℝ) :
    |Real.sqrt (C / k) * Real.tanh φ0| < Real.sqrt (C / k) :=
```

### `tanh_cannot_match_large_data`
For y₀ > √(C/k) no φ₀ gives y(0) = y₀: formula covers only small data.

```lean
theorem tanh_cannot_match_large_data {C k y0 : ℝ} (hy0 : Real.sqrt (C / k) < y0) :
    ∀ φ0 : ℝ, Real.sqrt (C / k) * Real.tanh φ0 ≠ y0 :=
```
