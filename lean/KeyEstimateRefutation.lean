/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

/-
  KeyEstimateRefutation.lean  —  Benjamin Stanley Frohman, 2026-11-09.

  Machine-checked parts of the refutation of the "key estimate"
      d/dt ‖ω(·,t)‖_{L∞} ≤ C − k·‖ω(·,t)‖_{L∞}²,  C ≥ 0, k > 0
  for 3D incompressible Navier–Stokes on T³ = (ℝ/2πℤ)³ with constants independent of the data.

  WHAT IS PROVED HERE (no `sorry`, no custom axioms):
  * Part 1 (abstract comparison): if a function g touches t ↦ ‖ω(·,t)‖_{L∞} from below at t = 0
    (g ≤ ‖ω(·,t)‖_{L∞} on [0,δ), g 0 = ‖ω(·,0)‖_{L∞}) and g'(0⁺) = r > C − k·‖ω(·,0)‖_{L∞}², then
    t ↦ ‖ω(·,t)‖_{L∞} cannot satisfy the
    estimate on any [0,T), T > 0 — neither in the differentiable form used in
    `FrohmanianTetherDraftAudit.lean` (`DraftRiccatiEstimate`, copied verbatim below) nor in the
    weaker upper-right-Dini form appropriate for an L∞ norm. In Lean the slot for
    t ↦ ‖ω(·,t)‖_{L∞} is the argument `vorticityLinfNorm` (and its derivative `vorticityLinfNorm'`);
    the lemmas hold for every real function in that slot.
  * Part 2 (the explicit field U, exact calculus on ℝ³): divergence-free, its curl,
    the global bound |∇×U|² ≤ 36 = |(∇×U)(0)|², and the exact value of the right-hand side of the
    vorticity equation at x = 0 for u₀ = A·U:  (0, 0, 6A(A − ν)).
  * Part 3 (arithmetic): for every ν > 0, C, k > 0 there is A > ν with 6A(A−ν) > C − k(6A)².

  WHAT IS NOT PROVED HERE (classical ingredients, cited in REPORT.md):
  * existence/uniqueness of a smooth solution on some [0,T) for smooth data on T³, and the
    fact that ω is C¹ in t up to t = 0 and satisfies the vorticity equation pointwise there;
  * hence the identification of g(t) := |ω(0,t)| as a C¹ function near t = 0 with
    g'(0) = (ω·∂ₜω)(0,0)/|ω(0,0)| = third component of the vorticity-equation RHS.
  * The V2 (localized, energy-dependent constants) maximum certificate is done in interval
    arithmetic (python-flint/Arb), not in Lean.
-/
import Mathlib

/-!
# lean.KeyEstimateRefutation

Machine-checked Lean 4 module.
-/

open Set Filter Topology Real

namespace KeyEstimate

/-! ## Part 1. Abstract comparison lemma -/

/-- Verbatim copy of the hypothesis in `FrohmanianTetherDraftAudit.lean`. -/
def DraftRiccatiEstimate (vorticityLinfNorm vorticityLinfNorm' : ℝ → ℝ) (C k T : ℝ) : Prop :=
  0 ≤ C ∧ 0 < k ∧ (∀ t ∈ Ico 0 T, HasDerivAt vorticityLinfNorm (vorticityLinfNorm' t) t) ∧
    (∀ t ∈ Ico 0 T, vorticityLinfNorm' t ≤ C - k * vorticityLinfNorm t ^ 2)

/-- Weaker, `L∞`-norm-appropriate form: the upper right Dini derivative of
`t ↦ ‖ω(·,t)‖_{L∞}` is `≤ C − k ‖ω(·,t)‖²_{L∞}`
on `[0,T)` (stated with an explicit ε–δ, no differentiability assumed). -/
def DiniRiccatiEstimate (vorticityLinfNorm : ℝ → ℝ) (C k T : ℝ) : Prop :=
  0 ≤ C ∧ 0 < k ∧ ∀ t ∈ Ico 0 T, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ioo t (t + δ),
    vorticityLinfNorm s ≤ vorticityLinfNorm t + (C - k * vorticityLinfNorm t ^ 2 + ε) * (s - t)

/-- If `g ≤ ‖ω(·,t)‖_{L∞}` on `[0,δ)`, `g 0 = ‖ω(·,0)‖_{L∞}`, and both have right derivatives at
`0`, then `g'(0⁺) ≤ (d/dt ‖ω(·,t)‖_{L∞})(0⁺)`. -/
theorem rightDeriv_le_of_touch {vorticityLinfNorm g : ℝ → ℝ} {m r δ : ℝ} (hδ : 0 < δ)
    (hM : HasDerivWithinAt vorticityLinfNorm m (Ici 0) 0) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = vorticityLinfNorm 0) (hle : ∀ t ∈ Ico 0 δ, g t ≤ vorticityLinfNorm t) : r ≤ m := by
  have h := hM.sub hg
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at h
  have hev : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), 0 ≤ slope (vorticityLinfNorm - g) 0 t := by
    have h1 : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), t < δ :=
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)
    have h2 : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), t ∈ Ioi (0:ℝ) := self_mem_nhdsWithin
    filter_upwards [h1, h2] with t ht1 ht2
    have htpos : 0 < t := ht2
    rw [slope_def_field]
    apply div_nonneg _ (by linarith)
    have := hle t ⟨htpos.le, ht1⟩
    simp only [Pi.sub_apply]
    linarith
  have := ge_of_tendsto h hev
  linarith

/-- **Refutation lemma (differentiable form).** -/
theorem draftRiccati_false_of_touch {vorticityLinfNorm vorticityLinfNorm' g : ℝ → ℝ} {C k T r : ℝ} (hT : 0 < T)
    (hR : DraftRiccatiEstimate vorticityLinfNorm vorticityLinfNorm' C k T) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = vorticityLinfNorm 0) (hle : ∀ t ∈ Ico 0 T, g t ≤ vorticityLinfNorm t) (hr : C - k * vorticityLinfNorm 0 ^ 2 < r) : False := by
  obtain ⟨_, _, hd, hi⟩ := hR
  have h0T : (0:ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hm := rightDeriv_le_of_touch hT (hd 0 h0T).hasDerivWithinAt hg h0 hle
  have := hi 0 h0T
  linarith

/-- **Refutation lemma (Dini form, no differentiability of `t ↦ ‖ω(·,t)‖_{L∞}` assumed).** -/
theorem diniRiccati_false_of_touch {vorticityLinfNorm g : ℝ → ℝ} {C k T r : ℝ} (hT : 0 < T)
    (hR : DiniRiccatiEstimate vorticityLinfNorm C k T) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = vorticityLinfNorm 0) (hle : ∀ t ∈ Ico 0 T, g t ≤ vorticityLinfNorm t) (hr : C - k * vorticityLinfNorm 0 ^ 2 < r) : False := by
  obtain ⟨_, _, hD⟩ := hR
  set ε := (r - (C - k * vorticityLinfNorm 0 ^ 2)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ, hδ, hup⟩ := hD 0 ⟨le_rfl, hT⟩ ε hεpos
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at hg
  have hev : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), slope g 0 t ≤ C - k * vorticityLinfNorm 0 ^ 2 + ε := by
    have h1 : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), t < min δ T :=
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hδ hT))
    have h2 : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), t ∈ Ioi (0:ℝ) := self_mem_nhdsWithin
    filter_upwards [h1, h2] with t ht1 ht2
    have htpos : 0 < t := ht2
    have htd : t < δ := lt_of_lt_of_le ht1 (min_le_left _ _)
    have htT : t < T := lt_of_lt_of_le ht1 (min_le_right _ _)
    have hMt := hup t ⟨htpos, by linarith⟩
    have hgt := hle t ⟨htpos.le, htT⟩
    rw [slope_def_field, div_le_iff₀ (by linarith)]
    simp only [sub_zero] at hMt ⊢
    linarith
  have := le_of_tendsto hg hev
  linarith

/-! ## Part 2. The explicit field  U = 3(−sin y, sin x, 0) + (−sin x cos z, 0, cos x sin z),
    initial datum u₀ = A·U.  Partial derivatives are `deriv` of coordinate slices. -/

noncomputable section

def u₁ (A x y z : ℝ) : ℝ := A * (-3 * Real.sin y - Real.sin x * Real.cos z)
def u₂ (A x _y _z : ℝ) : ℝ := A * (3 * Real.sin x)
def u₃ (A x _y z : ℝ) : ℝ := A * (Real.cos x * Real.sin z)

def dx (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f s y z) x
def dy (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f x s z) y
def dz (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f x y s) z

theorem div_free (A x y z : ℝ) : dx (u₁ A) x y z + dy (u₂ A) x y z + dz (u₃ A) x y z = 0 := by
  simp [dx, dy, dz, u₁, u₂, u₃]

/-- vorticity ω = ∇×u₀ = ∇×(A·U), components `ω₁, ω₂, ω₃`, from the definition -/
def ω₁ (A : ℝ) (x y z : ℝ) : ℝ := dy (u₃ A) x y z - dz (u₂ A) x y z
def ω₂ (A : ℝ) (x y z : ℝ) : ℝ := dz (u₁ A) x y z - dx (u₃ A) x y z
def ω₃ (A : ℝ) (x y z : ℝ) : ℝ := dx (u₂ A) x y z - dy (u₁ A) x y z

theorem ω₁_eq (A : ℝ) : ω₁ A = fun _ _ _ => 0 := by
  funext x y z; simp [ω₁, dy, dz, u₂, u₃]
theorem ω₂_eq (A : ℝ) : ω₂ A = fun x _ z => A * (2 * Real.sin x * Real.sin z) := by
  funext x y z; simp [ω₂, dx, dz, u₁, u₃]; ring
theorem ω₃_eq (A : ℝ) : ω₃ A = fun x y _ => A * (3 * (Real.cos x + Real.cos y)) := by
  funext x y z; simp [ω₃, dx, dy, u₁, u₂]; ring

/-- **Global maximum certificate**: |∇×U|² ≤ 36 everywhere (∇×U = ω/A), and |(∇×U)(0)|² = 36. -/
theorem omega_sq_le (x y z : ℝ) :
    (2 * Real.sin x * Real.sin z) ^ 2 + (3 * (Real.cos x + Real.cos y)) ^ 2 ≤ 36 := by
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hz := Real.sin_sq_add_cos_sq z
  nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin y), sq_nonneg (Real.cos z),
    mul_nonneg (sq_nonneg (Real.sin x)) (sq_nonneg (Real.cos z)), sq_nonneg (Real.sin x)]

theorem omega_at_origin (A : ℝ) : ω₁ A 0 0 0 = 0 ∧ ω₂ A 0 0 0 = 0 ∧ ω₃ A 0 0 0 = 6 * A := by
  rw [ω₁_eq, ω₂_eq, ω₃_eq]; simp; ring

/-- `|ω(x,0)| ≤ 6|A|` everywhere, with equality at the origin: `‖ω(·,0)‖∞ = 6|A|`. -/
theorem omega_norm_bound (A x y z : ℝ) :
    Real.sqrt (ω₁ A x y z ^ 2 + ω₂ A x y z ^ 2 + ω₃ A x y z ^ 2) ≤ 6 * |A| := by
  rw [ω₁_eq, ω₂_eq, ω₃_eq]
  simp only
  rw [Real.sqrt_le_left (by positivity)]
  have h := omega_sq_le x y z
  have hA : |A| ^ 2 = A ^ 2 := sq_abs A
  have e : (0:ℝ) ^ 2 + (A * (2 * Real.sin x * Real.sin z)) ^ 2 + (A * (3 * (Real.cos x + Real.cos y))) ^ 2
      = A ^ 2 * ((2 * Real.sin x * Real.sin z) ^ 2 + (3 * (Real.cos x + Real.cos y)) ^ 2) := by ring
  rw [e]
  have : (6 * |A|) ^ 2 = A ^ 2 * 36 := by rw [mul_pow, hA]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg A)

def lap (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => deriv (fun r => f r y z) s) x + deriv (fun s => deriv (fun r => f x r z) s) y +
    deriv (fun s => deriv (fun r => f x y r) s) z

/-- i-th component of the vorticity-equation RHS  (ω·∇)uᵢ − (u·∇)ωᵢ + νΔωᵢ. -/
def rhs (A ν : ℝ) (ωᵢ : ℝ → ℝ → ℝ → ℝ) (uᵢ : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (ω₁ A x y z * dx uᵢ x y z + ω₂ A x y z * dy uᵢ x y z + ω₃ A x y z * dz uᵢ x y z)
  - (u₁ A x y z * dx ωᵢ x y z + u₂ A x y z * dy ωᵢ x y z + u₃ A x y z * dz ωᵢ x y z)
  + ν * lap ωᵢ x y z

theorem rhs_origin (A ν : ℝ) :
    rhs A ν (ω₁ A) (u₁ A) 0 0 0 = 0 ∧ rhs A ν (ω₂ A) (u₂ A) 0 0 0 = 0 ∧
    rhs A ν (ω₃ A) (u₃ A) 0 0 0 = 6 * A * (A - ν) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [rhs, ω₁_eq, ω₂_eq, ω₃_eq, lap, dx, dy, dz, u₁, u₂, u₃]
    simp
    try ring

/-! ## Part 3. Arithmetic: the comparison inequality fails for large amplitude. -/

theorem amplitude_exists (ν C k : ℝ) (hν : 0 < ν) (hk : 0 < k) :
    ∃ A : ℝ, ν < A ∧ C - k * (6 * A) ^ 2 < 6 * A * (A - ν) := by
  have hq : 0 ≤ |C| / k := div_nonneg (abs_nonneg C) hk.le
  refine ⟨ν + 1 + |C| / k, by linarith, ?_⟩
  set A := ν + 1 + |C| / k with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hCA : |C| ≤ k * A := by
    have h1 : |C| / k ≤ A := by rw [hA]; linarith
    have h2 : |C| = |C| / k * k := (div_mul_cancel₀ _ hk.ne').symm
    calc |C| = |C| / k * k := h2
      _ ≤ A * k := mul_le_mul_of_nonneg_right h1 hk.le
      _ = k * A := by ring
  have hC : C ≤ |C| := le_abs_self C
  have hpos : 0 < 6 * A * (A - ν) := by
    have : 0 < A - ν := by rw [hA]; linarith
    have : 0 < A := by linarith
    positivity
  have hkA : k * A ≤ k * (6 * A) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  linarith

/-- Scalar step of the V2 (localized-family) argument: with `‖ω(·,0)‖_{L∞} = 120νλ²` and touching-function
derivative `1200ν²λ⁴` (values from REPORT.md §V2, established by exact symbolic computation and
an interval-arithmetic certificate, NOT in Lean), the estimate is violated once
`1200ν²λ⁴ ≥ C`. -/
theorem localized_family_violation (ν C k L : ℝ) (hν : 0 < ν) (hk : 0 < k) (hL : 0 < L)
    (hbig : C ≤ 1200 * ν ^ 2 * L ^ 4) :
    C - k * (120 * ν * L ^ 2) ^ 2 < 1200 * ν ^ 2 * L ^ 4 := by
  have : 0 < k * (120 * ν * L ^ 2) ^ 2 := by positivity
  linarith

end

end KeyEstimate

#print axioms KeyEstimate.rightDeriv_le_of_touch
#print axioms KeyEstimate.draftRiccati_false_of_touch
#print axioms KeyEstimate.diniRiccati_false_of_touch
#print axioms KeyEstimate.div_free
#print axioms KeyEstimate.w1_eq
#print axioms KeyEstimate.w2_eq
#print axioms KeyEstimate.w3_eq
#print axioms KeyEstimate.omega_sq_le
#print axioms KeyEstimate.omega_at_origin
#print axioms KeyEstimate.omega_norm_bound
#print axioms KeyEstimate.rhs_origin
#print axioms KeyEstimate.amplitude_exists
#print axioms KeyEstimate.localized_family_violation
