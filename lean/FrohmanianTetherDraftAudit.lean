/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Mathlib

/-!
# lean.FrohmanianTetherDraftAudit

Machine-checked Lean 4 module.
-/

open Set MeasureTheory intervalIntegral Filter
open scoped Topology Matrix

noncomputable section

namespace FrohmanianTetherDraftAudit

/-! ## Part 1. The conditional chain (fully proved) -/

/-- Riccati comparison (barrier argument). If `d/dt ‖ω(·,t)‖_{L∞} ≤ C − k ‖ω(·,t)‖²_{L∞}` on
`[0,T)` with `C ≥ 0`, `k > 0`, then `‖ω(·,t)‖_{L∞} ≤ max (‖ω(·,0)‖_{L∞}) (√(C/k))` on `[0,T)`.
(Proved for every real function in the slot `vorticityLinfNorm`.) Holds for every real `T`. -/
theorem riccati_comparison {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {C k T : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt vorticityLinfNorm (vorticityLinfNorm' t) t)
    (hineq : ∀ t ∈ Ico 0 T, vorticityLinfNorm' t ≤ C - k * vorticityLinfNorm t ^ 2) :
    ∀ t ∈ Ico 0 T, vorticityLinfNorm t ≤ max (vorticityLinfNorm 0) (Real.sqrt (C / k)) := by
  intro t ht
  set K := max (vorticityLinfNorm 0) (Real.sqrt (C / k)) with hK
  have hsqrt_le : Real.sqrt (C / k) ≤ K := le_max_right _ _
  have hsqrt_nn : 0 ≤ Real.sqrt (C / k) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (C / k) ^ 2 = C / k := Real.sq_sqrt (div_nonneg hC hk.le)
  -- for every ε > 0, vorticityLinfNorm t ≤ K + ε
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have hsub : Icc 0 t ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hcont : ContinuousOn vorticityLinfNorm (Icc 0 t) :=
    fun x hx => (hderiv x (hsub hx)).continuousAt.continuousWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := vorticityLinfNorm) (f' := vorticityLinfNorm') (a := 0) (b := t)
    hcont (fun x hx => (hderiv x (hsub (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (B := fun _ => K + ε / 2) (B' := fun _ => 0)
    (by have := le_max_left (vorticityLinfNorm 0) (Real.sqrt (C / k)); simp only; linarith [half_pos hε])
    continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _)
    (by
      intro x hx hMx
      simp only at hMx ⊢
      have h1 : Real.sqrt (C / k) < vorticityLinfNorm x := by linarith [half_pos hε]
      have h2 : C / k < vorticityLinfNorm x ^ 2 := by
        rw [← hsq]; exact pow_lt_pow_left₀ h1 hsqrt_nn (by norm_num)
      have h3 : C < k * vorticityLinfNorm x ^ 2 := by
        rw [div_lt_iff₀ hk] at h2; linarith
      have := hineq x (hsub (Ico_subset_Icc_self hx))
      linarith)
    (right_mem_Icc.mpr ht.1)
  have : vorticityLinfNorm t ≤ K + ε / 2 := key
  linarith [half_pos hε]

/-- Global-in-time version (the case "T = ∞"): hypotheses on `[0,∞)`. -/
theorem riccati_comparison_global {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {C k : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt vorticityLinfNorm (vorticityLinfNorm' t) t)
    (hineq : ∀ t ∈ Ici (0:ℝ), vorticityLinfNorm' t ≤ C - k * vorticityLinfNorm t ^ 2) :
    ∀ t ∈ Ici (0:ℝ), vorticityLinfNorm t ≤ max (vorticityLinfNorm 0) (Real.sqrt (C / k)) := by
  intro t ht
  exact riccati_comparison (T := t + 1) hC hk
    (fun s hs => hderiv s hs.1) (fun s hs => hineq s hs.1) t ⟨ht, by linarith⟩

/-- The comparison bound is nonnegative. -/
lemma riccati_bound_nonneg (vorticityLinfNorm₀ C k : ℝ) : 0 ≤ max vorticityLinfNorm₀ (Real.sqrt (C / k)) :=
  le_trans (Real.sqrt_nonneg _) (le_max_right _ _)

/-- Finite BKM integral: under the Riccati hypothesis,
`∫₀ᵗ ‖ω(·,s)‖_{L∞} ds ≤ max(‖ω(·,0)‖_{L∞}, √(C/k)) · t`. -/
theorem riccati_integral_bound {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {C k T : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt vorticityLinfNorm (vorticityLinfNorm' t) t)
    (hineq : ∀ t ∈ Ico 0 T, vorticityLinfNorm' t ≤ C - k * vorticityLinfNorm t ^ 2) :
    ∀ t ∈ Ico 0 T, ∫ s in (0:ℝ)..t, vorticityLinfNorm s ≤ max (vorticityLinfNorm 0) (Real.sqrt (C / k)) * t := by
  intro t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hcont : ContinuousOn vorticityLinfNorm (Icc 0 t) :=
    fun x hx => (hderiv x (hsub hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable vorticityLinfNorm volume 0 t := hcont.intervalIntegrable_of_Icc ht.1
  have hmono := intervalIntegral.integral_mono_on ht.1 hint
    (intervalIntegral.intervalIntegrable_const (c := max (vorticityLinfNorm 0) (Real.sqrt (C / k))))
    (fun x hx => riccati_comparison hC hk hderiv hineq x (hsub hx))
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmono

/-- **The draft's key estimate, as an explicit OPEN hypothesis.**
`DraftRiccatiEstimate vorticityLinfNorm vorticityLinfNorm' C k T` says: `t ↦ ‖ω(·,t)‖_{L∞}`
(the argument `vorticityLinfNorm`) is differentiable on `[0,T)` with derivative `vorticityLinfNorm'`,
and `d/dt ‖ω(·,t)‖_{L∞} ≤ C − k·‖ω(·,t)‖²_{L∞}` there, with `C ≥ 0`, `k > 0`.

WARNING: this is NOT derived from the Navier–Stokes equations, in this file or in the draft.
A uniform-in-time inequality of this form for the vorticity sup-norm of arbitrary smooth
solutions of 3D Navier–Stokes would immediately give global regularity; establishing it is
essentially as hard as the Clay Millennium Problem itself. -/
def DraftRiccatiEstimate (vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ) (C k T : ℝ) : Prop :=
  0 ≤ C ∧ 0 < k ∧ (∀ t ∈ Ico 0 T, HasDerivAt vorticityLinfNorm (vorticityLinfNorm' t) t) ∧
    (∀ t ∈ Ico 0 T, vorticityLinfNorm' t ≤ C - k * vorticityLinfNorm t ^ 2)

/-- Boundedness of the BKM integral `∫₀ᵗ ‖ω(·,s)‖_{L∞} ds` on `[0,T*)`. -/
def BKMIntegralBounded (vorticityLinfNorm : ℝ → ℝ) (Tstar : ℝ) : Prop :=
  ∃ B : ℝ, ∀ t ∈ Ico 0 Tstar, ∫ s in (0:ℝ)..t, vorticityLinfNorm s ≤ B

/-- **BKM continuation criterion, as an explicit hypothesis** (Beale–Kato–Majda, cited, not
proved here). `Extends Tstar` is an abstract proposition meaning "the solution extends smoothly
past `Tstar`". The criterion in contrapositive form: if `Tstar < ∞` were a genuine blow-up time
then `∫₀^{Tstar} ‖ω(·,s)‖_{L∞} ds = ∞`; equivalently, a bounded BKM integral on `[0,Tstar)` implies extension. -/
def BKMContinuation (vorticityLinfNorm : ℝ → ℝ) (Extends : ℝ → Prop) (Tstar : ℝ) : Prop :=
  BKMIntegralBounded vorticityLinfNorm Tstar → Extends Tstar

/-- The Riccati hypothesis yields a bounded BKM integral on `[0,T*)`. -/
theorem draftRiccati_implies_BKMIntegralBounded {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {C k Tstar : ℝ}
    (hR : DraftRiccatiEstimate vorticityLinfNorm vorticityLinfNorm' C k Tstar) : BKMIntegralBounded vorticityLinfNorm Tstar := by
  obtain ⟨hC, hk, hd, hi⟩ := hR
  refine ⟨max (vorticityLinfNorm 0) (Real.sqrt (C / k)) * Tstar, fun t ht => ?_⟩
  have h1 := riccati_integral_bound hC hk hd hi t ht
  have h2 : max (vorticityLinfNorm 0) (Real.sqrt (C / k)) * t ≤ max (vorticityLinfNorm 0) (Real.sqrt (C / k)) * Tstar :=
    mul_le_mul_of_nonneg_left ht.2.le (riccati_bound_nonneg _ _ _)
  linarith

/-- **Conditional continuation.** Draft Riccati hypothesis + BKM hypothesis ⇒ extension past
`Tstar`, for every finite `Tstar`. -/
theorem conditional_extension {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {Extends : ℝ → Prop} {C k Tstar : ℝ}
    (hR : DraftRiccatiEstimate vorticityLinfNorm vorticityLinfNorm' C k Tstar) (hBKM : BKMContinuation vorticityLinfNorm Extends Tstar) :
    Extends Tstar :=
  hBKM (draftRiccati_implies_BKMIntegralBounded hR)

/-- **Conditional "global regularity" (the draft's Theorem 6.1, honestly stated).**
If the open estimate and the BKM criterion hold for every finite horizon, then the solution
extends past every finite time. Both inputs are hypotheses; neither is proved for 3D NS. -/
theorem conditional_no_finite_blowup {vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ} {Extends : ℝ → Prop} {C k : ℝ}
    (hR : ∀ Tstar : ℝ, DraftRiccatiEstimate vorticityLinfNorm vorticityLinfNorm' C k Tstar)
    (hBKM : ∀ Tstar : ℝ, BKMContinuation vorticityLinfNorm Extends Tstar) :
    ∀ Tstar : ℝ, Extends Tstar :=
  fun Tstar => conditional_extension (hR Tstar) (hBKM Tstar)

/-! ## Part 2. Machine-checked refutations of draft claims -/

section Tether

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `L²`-orthogonal projection off `u`: `P⊥ Φ = Φ − (⟨Φ,u⟩/‖u‖²) u`. -/
def projPerp (u Φ : V) : V := Φ - (inner ℝ Φ u / ‖u‖ ^ 2) • u

/-- Tether metric correction `B(F,G) = −κ ‖ω‖²_{L²} ⟨P⊥ dF, P⊥ dG⟩` (the draft wrote `W` for the
enstrophy `‖ω‖²_{L²} = ∫|ω|²`; here it is the real argument `enstrophy`). -/
def tetherB (κ enstrophy : ℝ) (u dF dG : V) : ℝ :=
  -κ * enstrophy * inner ℝ (projPerp u dF) (projPerp u dG)

lemma projPerp_self (u : V) : projPerp u u = 0 := by
  unfold projPerp
  by_cases hu : u = 0
  · simp [hu]
  · have hn : ‖u‖ ^ 2 ≠ 0 := by positivity
    rw [real_inner_self_eq_norm_sq, div_self hn, one_smul, sub_self]

/-- (2a) The tether is symmetric. -/
theorem tetherB_symm (κ enstrophy : ℝ) (u dF dG : V) :
    tetherB κ enstrophy u dF dG = tetherB κ enstrophy u dG dF := by
  unfold tetherB; rw [real_inner_comm]

/-- Strict degeneracy: `B(F,H) = 0` when `dH = u`. -/
theorem tetherB_degenerate_H (κ enstrophy : ℝ) (u dF : V) : tetherB κ enstrophy u dF u = 0 := by
  simp [tetherB, projPerp_self]

/-- (2a) If `κ ≠ 0`, `enstrophy ≠ 0` and `v` is not parallel to `u` (i.e. `P⊥ v ≠ 0`), then
`B(v,v) ≠ 0`. -/
theorem tetherB_diag_ne_zero {κ enstrophy : ℝ} (hκ : κ ≠ 0) (henstrophy : enstrophy ≠ 0) (u v : V)
    (hv : projPerp u v ≠ 0) : tetherB κ enstrophy u v v ≠ 0 := by
  unfold tetherB
  have : inner ℝ (projPerp u v) (projPerp u v) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; positivity
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hκ) henstrophy) this

/-- (2a) **Refutes A1 / Lemma 3:** under the same conditions the tether is NOT antisymmetric. -/
theorem tetherB_not_antisymm {κ enstrophy : ℝ} (hκ : κ ≠ 0) (henstrophy : enstrophy ≠ 0) (u v : V)
    (hv : projPerp u v ≠ 0) :
    ¬ ∀ dF dG : V, tetherB κ enstrophy u dF dG = -tetherB κ enstrophy u dG dF := by
  intro h
  have h1 := h v v
  have h2 : tetherB κ enstrophy u v v = 0 := by linarith
  exact tetherB_diag_ne_zero hκ henstrophy u v hv h2

/-- (2a) Concrete witness in `EuclideanSpace ℝ (Fin 2)`: `u = e₁`, `dF = e₂`. -/
theorem tetherB_not_antisymm_R2 {κ enstrophy : ℝ} (hκ : κ ≠ 0) (henstrophy : enstrophy ≠ 0) :
    tetherB κ enstrophy (EuclideanSpace.single (0 : Fin 2) (1:ℝ)) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) ≠ 0 ∧
    ¬ ∀ dF dG : EuclideanSpace ℝ (Fin 2),
      tetherB κ enstrophy (EuclideanSpace.single 0 1) dF dG
        = -tetherB κ enstrophy (EuclideanSpace.single 0 1) dG dF := by
  have hp : projPerp (EuclideanSpace.single (0 : Fin 2) (1:ℝ))
      (EuclideanSpace.single 1 1) = EuclideanSpace.single 1 1 := by
    unfold projPerp
    simp [EuclideanSpace.inner_single_left]
  have hne : projPerp (EuclideanSpace.single (0 : Fin 2) (1:ℝ))
      (EuclideanSpace.single 1 1) ≠ 0 := by
    rw [hp]; intro h
    have := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h
    simp at this
  exact ⟨tetherB_diag_ne_zero hκ henstrophy _ _ hne, tetherB_not_antisymm hκ henstrophy _ _ hne⟩

end Tether

/-! ### (2b) The draft's "tether 2-form" on ℝ³ is not antisymmetric -/

/-- The draft's tether 2-form `T(a,b) = ω·(a×b) − κ|ω|²(a·b)` on `Fin 3 → ℝ`. -/
def tether2Form (κ : ℝ) (ω a b : Fin 3 → ℝ) : ℝ :=
  ω ⬝ᵥ (a ×₃ b) - κ * (ω ⬝ᵥ ω) * (a ⬝ᵥ b)

/-- The classical Arnold part alone IS antisymmetric. -/
theorem arnold_part_antisymm (ω a b : Fin 3 → ℝ) :
    ω ⬝ᵥ (a ×₃ b) = -(ω ⬝ᵥ (b ×₃ a)) := by
  rw [← neg_cross, dotProduct_neg]

/-- `T(ω,ω) = −κ |ω|⁴ ≠ 0` when `κ ≠ 0`, `ω ≠ 0`. -/
theorem tether2Form_diag_ne_zero {κ : ℝ} (hκ : κ ≠ 0) {ω : Fin 3 → ℝ} (hω : ω ≠ 0) :
    tether2Form κ ω ω ω ≠ 0 := by
  unfold tether2Form
  have h : ω ⬝ᵥ ω ≠ 0 := fun h => hω (dotProduct_self_eq_zero.mp h)
  rw [cross_self, dotProduct_zero, zero_sub, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hκ h) h

/-- **Refutes Theorem 4.1 / Lemma 3:** the tether 2-form is not antisymmetric, hence not a
symplectic (or any differential) 2-form, whenever `κ ≠ 0` and `ω ≠ 0`. -/
theorem tether2Form_not_antisymm {κ : ℝ} (hκ : κ ≠ 0) {ω : Fin 3 → ℝ} (hω : ω ≠ 0) :
    ¬ ∀ a b : Fin 3 → ℝ, tether2Form κ ω a b = -tether2Form κ ω b a := by
  intro h
  have h1 := h ω ω
  exact tether2Form_diag_ne_zero hκ hω (by linarith)

/-! ### (2c) Degeneracy kills feedback -/

section Feedback

variable {State V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Generator of the draft's evolution: `dF/dt = {F,H}_LP + [F,H]_diss + B(F,H)`.
All ingredients are explicit arguments: `LP`, `diss` brackets, functional derivative `grad`,
enstrophy `enstrophy` (`‖ω‖²_{L²}` as a function of the state), velocity `vel`, Hamiltonian `H`. -/
def tetherGenerator (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ) (grad : (State → ℝ) → State → V)
    (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ) (κ : ℝ) (F : State → ℝ) (ω : State) : ℝ :=
  LP F H ω + diss F H ω + tetherB κ (enstrophy ω) (vel ω) (grad F ω) (grad H ω)

/-- If `δH/δω = u` (hypothesis `hH`), the generator equals the classical one for every `κ`. -/
theorem generator_eq_classical (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ)
    (grad : (State → ℝ) → State → V) (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (F : State → ℝ) (ω : State) :
    tetherGenerator LP diss grad enstrophy vel H κ F ω = LP F H ω + diss F H ω := by
  unfold tetherGenerator; rw [hH, tetherB_degenerate_H, add_zero]

/-- The generator is independent of `κ`. -/
theorem generator_indep_kappa (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ)
    (grad : (State → ℝ) → State → V) (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ₁ κ₂ : ℝ) (F : State → ℝ) (ω : State) :
    tetherGenerator LP diss grad enstrophy vel H κ₁ F ω = tetherGenerator LP diss grad enstrophy vel H κ₂ F ω := by
  rw [generator_eq_classical LP diss grad enstrophy vel H hH, generator_eq_classical LP diss grad enstrophy vel H hH]

/-- `γ` is a (weak) trajectory of the `κ`-tethered evolution: for every observable `F`,
`d/dt F(γ t) = generator κ F (γ t)`. -/
def IsTetherFlow (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ) (grad : (State → ℝ) → State → V)
    (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ) (κ : ℝ) (γ : ℝ → State) : Prop :=
  ∀ (F : State → ℝ) (t : ℝ), HasDerivAt (fun s => F (γ s)) (tetherGenerator LP diss grad enstrophy vel H κ F (γ t)) t

/-- The set of trajectories is the same for every `κ`: the tether never changes the flow. -/
theorem isTetherFlow_iff (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ)
    (grad : (State → ℝ) → State → V) (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ₁ κ₂ : ℝ) (γ : ℝ → State) :
    IsTetherFlow LP diss grad enstrophy vel H κ₁ γ ↔ IsTetherFlow LP diss grad enstrophy vel H κ₂ γ := by
  unfold IsTetherFlow
  simp only [generator_indep_kappa LP diss grad enstrophy vel H hH κ₁ κ₂]

/-- **Degeneracy kills feedback (refutes A3/A5 + Prop. 4.1).** For any observable `Mfun`
(e.g. a smooth surrogate of `‖ω‖_∞`) along a `κ`-tethered trajectory, its time derivative
equals the derivative under the classical (`κ = 0`) generator. Hence any differential
inequality — in particular the draft's `d/dt ‖ω(·,t)‖_{L∞} ≤ C − k ‖ω(·,t)‖²_{L∞}` — holds for the tethered flow iff it
holds for the unmodified flow: the "negative quadratic feedback" cannot come from the tether. -/
theorem observable_deriv_indep_kappa (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ)
    (grad : (State → ℝ) → State → V) (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (γ : ℝ → State)
    (hγ : IsTetherFlow LP diss grad enstrophy vel H κ γ) (Mfun : State → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Mfun (γ s)) (tetherGenerator LP diss grad enstrophy vel H 0 Mfun (γ t)) t ∧
    HasDerivAt (fun s => Mfun (γ s)) (LP Mfun H (γ t) + diss Mfun H (γ t)) t := by
  have h := hγ Mfun t
  rw [generator_indep_kappa LP diss grad enstrophy vel H hH κ 0] at h
  exact ⟨h, by rwa [generator_eq_classical LP diss grad enstrophy vel H hH] at h⟩

/-- Corollary: the draft's Riccati estimate for an observable along a tethered trajectory is
literally the same proposition for every `κ` (including the classical `κ = 0`). -/
theorem draftRiccati_tether_iff_classical (LP diss : (State → ℝ) → (State → ℝ) → State → ℝ)
    (grad : (State → ℝ) → State → V) (enstrophy : State → ℝ) (vel : State → V) (H : State → ℝ)
    (hH : ∀ ω, grad H ω = vel ω) (κ : ℝ) (γ : ℝ → State) (Mfun : State → ℝ) (C k T : ℝ) :
    DraftRiccatiEstimate (fun s => Mfun (γ s))
        (fun s => tetherGenerator LP diss grad enstrophy vel H κ Mfun (γ s)) C k T ↔
      DraftRiccatiEstimate (fun s => Mfun (γ s))
        (fun s => tetherGenerator LP diss grad enstrophy vel H 0 Mfun (γ s)) C k T := by
  simp only [generator_indep_kappa LP diss grad enstrophy vel H hH κ 0]

end Feedback

/-! ### (2d) The tanh formula only covers small initial data -/

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [hfun] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  have := Real.cosh_sq x
  nlinarith [this]

lemma abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x),
    div_lt_one (Real.cosh_pos x)]
  have h := Real.cosh_sq x
  have hc := Real.cosh_pos x
  have : |Real.sinh x| ^ 2 < Real.cosh x ^ 2 := by rw [sq_abs]; linarith
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _) hc.le (by norm_num)).mp this

/-- The draft's formula `y(t) = √(C/k) tanh(√(Ck) t + φ₀)` solves `y' = C − k y²`. -/
theorem tanh_solves_riccati {C k : ℝ} (hC : 0 ≤ C) (hk : 0 < k) (φ0 t : ℝ) :
    HasDerivAt (fun s => Real.sqrt (C / k) * Real.tanh (Real.sqrt (C * k) * s + φ0))
      (C - k * (Real.sqrt (C / k) * Real.tanh (Real.sqrt (C * k) * t + φ0)) ^ 2) t := by
  have hlin : HasDerivAt (fun s => Real.sqrt (C * k) * s + φ0) (Real.sqrt (C * k)) t := by
    simpa using ((hasDerivAt_id t).const_mul (Real.sqrt (C * k))).add_const φ0
  have h := ((hasDerivAt_tanh (Real.sqrt (C * k) * t + φ0)).comp t hlin).const_mul
    (Real.sqrt (C / k))
  convert h using 1
  have hab : Real.sqrt (C / k) * Real.sqrt (C * k) = C := by
    rw [← Real.sqrt_mul (div_nonneg hC hk.le), show C / k * (C * k) = C ^ 2 by
      field_simp; ring, Real.sqrt_sq hC]
  have hsq : Real.sqrt (C / k) ^ 2 = C / k := Real.sq_sqrt (div_nonneg hC hk.le)
  have hk2 : k * (C / k) = C := by field_simp
  set τ := Real.tanh (Real.sqrt (C * k) * t + φ0)
  calc C - k * (Real.sqrt (C / k) * τ) ^ 2 = C - (k * Real.sqrt (C / k) ^ 2) * τ ^ 2 := by ring
    _ = C * (1 - τ ^ 2) := by rw [hsq, hk2]; ring
    _ = Real.sqrt (C / k) * ((1 - τ ^ 2) * Real.sqrt (C * k)) := by
        rw [show C * (1 - τ ^ 2) = (Real.sqrt (C / k) * Real.sqrt (C * k)) * (1 - τ ^ 2) by
          rw [hab]]
        ring

/-- Every initial value reachable by the tanh formula satisfies `|y(0)| ≤ √(C/k)`. -/
theorem tanh_initial_le {C k : ℝ} (φ0 : ℝ) :
    |Real.sqrt (C / k) * Real.tanh φ0| ≤ Real.sqrt (C / k) := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (abs_tanh_lt_one φ0).le

/-- With `C > 0` the tanh formula reaches only `|y(0)| < √(C/k)` (strictly). -/
theorem tanh_initial_lt {C k : ℝ} (hC : 0 < C) (hk : 0 < k) (φ0 : ℝ) :
    |Real.sqrt (C / k) * Real.tanh φ0| < Real.sqrt (C / k) := by
  have hpos : 0 < Real.sqrt (C / k) := Real.sqrt_pos.mpr (div_pos hC hk)
  rw [abs_mul, abs_of_pos hpos]
  exact mul_lt_of_lt_one_right hpos (abs_tanh_lt_one φ0)

/-- **Refutes the generality of Prop. 4.1's tanh formula:** for `y₀ > √(C/k)` no phase `φ₀`
gives `y(0) = y₀`. So the draft's explicit bound covers only small initial data. (The
general comparison bound `max(y₀, √(C/k))` of `riccati_comparison` does cover large data.) -/
theorem tanh_cannot_match_large_data {C k y0 : ℝ} (hy0 : Real.sqrt (C / k) < y0) :
    ∀ φ0 : ℝ, Real.sqrt (C / k) * Real.tanh φ0 ≠ y0 := by
  intro φ0 h
  have := tanh_initial_le (C := C) (k := k) φ0
  rw [h] at this
  linarith [le_abs_self y0]

end FrohmanianTetherDraftAudit
