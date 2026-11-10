/-
  KeyEstimateRefutation.lean  —  Benjamin Stanley Frohman, 2026-11-09.

  Machine-checked parts of the refutation of the "key estimate"
      M'(t) ≤ C − k·M(t)²,   M(t) = ‖ω(·,t)‖_{L∞},  C ≥ 0, k > 0
  for 3D incompressible Navier–Stokes on T³ = (ℝ/2πℤ)³ with constants independent of the data.

  WHAT IS PROVED HERE (no `sorry`, no custom axioms):
  * Part 1 (abstract comparison): if a function g touches M from below at t = 0
    (g ≤ M on [0,δ), g 0 = M 0) and g'(0⁺) = r > C − k·M(0)², then M cannot satisfy the
    estimate on any [0,T), T > 0 — neither in the differentiable form used in
    `FrohmanianTetherDraftAudit.lean` (`DraftRiccatiEstimate`, copied verbatim below) nor in the
    weaker upper-right-Dini form appropriate for a sup-norm.
  * Part 2 (the explicit field U, exact calculus on ℝ³): divergence-free, its curl,
    the global bound |Ω|² ≤ 36 = |Ω(0)|², and the exact value of the right-hand side of the
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

open Set Filter Topology Real

namespace KeyEstimate

/-! ## Part 1. Abstract comparison lemma -/

/-- Verbatim copy of the hypothesis in `FrohmanianTetherDraftAudit.lean`. -/
def DraftRiccatiEstimate (M M' : ℝ → ℝ) (C k T : ℝ) : Prop :=
  0 ≤ C ∧ 0 < k ∧ (∀ t ∈ Ico 0 T, HasDerivAt M (M' t) t) ∧
    (∀ t ∈ Ico 0 T, M' t ≤ C - k * M t ^ 2)

/-- Weaker, sup-norm-appropriate form: the upper right Dini derivative of `M` is `≤ C − k M²`
on `[0,T)` (stated with an explicit ε–δ, no differentiability assumed). -/
def DiniRiccatiEstimate (M : ℝ → ℝ) (C k T : ℝ) : Prop :=
  0 ≤ C ∧ 0 < k ∧ ∀ t ∈ Ico 0 T, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ioo t (t + δ),
    M s ≤ M t + (C - k * M t ^ 2 + ε) * (s - t)

/-- If `g ≤ M` on `[0,δ)`, `g 0 = M 0`, and both have right derivatives at `0`, then
`g'(0⁺) ≤ M'(0⁺)`. -/
theorem rightDeriv_le_of_touch {M g : ℝ → ℝ} {m r δ : ℝ} (hδ : 0 < δ)
    (hM : HasDerivWithinAt M m (Ici 0) 0) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = M 0) (hle : ∀ t ∈ Ico 0 δ, g t ≤ M t) : r ≤ m := by
  have h := hM.sub hg
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at h
  have hev : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), 0 ≤ slope (M - g) 0 t := by
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
theorem draftRiccati_false_of_touch {M M' g : ℝ → ℝ} {C k T r : ℝ} (hT : 0 < T)
    (hR : DraftRiccatiEstimate M M' C k T) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = M 0) (hle : ∀ t ∈ Ico 0 T, g t ≤ M t) (hr : C - k * M 0 ^ 2 < r) : False := by
  obtain ⟨_, _, hd, hi⟩ := hR
  have h0T : (0:ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hm := rightDeriv_le_of_touch hT (hd 0 h0T).hasDerivWithinAt hg h0 hle
  have := hi 0 h0T
  linarith

/-- **Refutation lemma (Dini form, no differentiability of `M` assumed).** -/
theorem diniRiccati_false_of_touch {M g : ℝ → ℝ} {C k T r : ℝ} (hT : 0 < T)
    (hR : DiniRiccatiEstimate M C k T) (hg : HasDerivWithinAt g r (Ici 0) 0)
    (h0 : g 0 = M 0) (hle : ∀ t ∈ Ico 0 T, g t ≤ M t) (hr : C - k * M 0 ^ 2 < r) : False := by
  obtain ⟨_, _, hD⟩ := hR
  set ε := (r - (C - k * M 0 ^ 2)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ, hδ, hup⟩ := hD 0 ⟨le_rfl, hT⟩ ε hεpos
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at hg
  have hev : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] (0:ℝ), slope g 0 t ≤ C - k * M 0 ^ 2 + ε := by
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

def u1 (A x y z : ℝ) : ℝ := A * (-3 * Real.sin y - Real.sin x * Real.cos z)
def u2 (A x _y _z : ℝ) : ℝ := A * (3 * Real.sin x)
def u3 (A x _y z : ℝ) : ℝ := A * (Real.cos x * Real.sin z)

def dx (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f s y z) x
def dy (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f x s z) y
def dz (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ := deriv (fun s => f x y s) z

theorem div_free (A x y z : ℝ) : dx (u1 A) x y z + dy (u2 A) x y z + dz (u3 A) x y z = 0 := by
  simp [dx, dy, dz, u1, u2, u3]

/-- vorticity ω = curl(A·U), from the definition -/
def w1 (A : ℝ) (x y z : ℝ) : ℝ := dy (u3 A) x y z - dz (u2 A) x y z
def w2 (A : ℝ) (x y z : ℝ) : ℝ := dz (u1 A) x y z - dx (u3 A) x y z
def w3 (A : ℝ) (x y z : ℝ) : ℝ := dx (u2 A) x y z - dy (u1 A) x y z

theorem w1_eq (A : ℝ) : w1 A = fun _ _ _ => 0 := by
  funext x y z; simp [w1, dy, dz, u2, u3]
theorem w2_eq (A : ℝ) : w2 A = fun x _ z => A * (2 * Real.sin x * Real.sin z) := by
  funext x y z; simp [w2, dx, dz, u1, u3]; ring
theorem w3_eq (A : ℝ) : w3 A = fun x y _ => A * (3 * (Real.cos x + Real.cos y)) := by
  funext x y z; simp [w3, dx, dy, u1, u2]; ring

/-- **Global maximum certificate**: |Ω|² ≤ 36 everywhere (Ω = ω/A), and |Ω(0)|² = 36. -/
theorem omega_sq_le (x y z : ℝ) :
    (2 * Real.sin x * Real.sin z) ^ 2 + (3 * (Real.cos x + Real.cos y)) ^ 2 ≤ 36 := by
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hz := Real.sin_sq_add_cos_sq z
  nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin y), sq_nonneg (Real.cos z),
    mul_nonneg (sq_nonneg (Real.sin x)) (sq_nonneg (Real.cos z)), sq_nonneg (Real.sin x)]

theorem omega_at_origin (A : ℝ) : w1 A 0 0 0 = 0 ∧ w2 A 0 0 0 = 0 ∧ w3 A 0 0 0 = 6 * A := by
  rw [w1_eq, w2_eq, w3_eq]; simp; ring

/-- `|ω(x,0)| ≤ 6|A|` everywhere, with equality at the origin: `‖ω(·,0)‖∞ = 6|A|`. -/
theorem omega_norm_bound (A x y z : ℝ) :
    Real.sqrt (w1 A x y z ^ 2 + w2 A x y z ^ 2 + w3 A x y z ^ 2) ≤ 6 * |A| := by
  rw [w1_eq, w2_eq, w3_eq]
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
def rhs (A ν : ℝ) (wi : ℝ → ℝ → ℝ → ℝ) (ui : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (w1 A x y z * dx ui x y z + w2 A x y z * dy ui x y z + w3 A x y z * dz ui x y z)
  - (u1 A x y z * dx wi x y z + u2 A x y z * dy wi x y z + u3 A x y z * dz wi x y z)
  + ν * lap wi x y z

theorem rhs_origin (A ν : ℝ) :
    rhs A ν (w1 A) (u1 A) 0 0 0 = 0 ∧ rhs A ν (w2 A) (u2 A) 0 0 0 = 0 ∧
    rhs A ν (w3 A) (u3 A) 0 0 0 = 6 * A * (A - ν) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [rhs, w1_eq, w2_eq, w3_eq, lap, dx, dy, dz, u1, u2, u3]
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

/-- Scalar step of the V2 (localized-family) argument: with `M₀ = 120νλ²` and touching-function
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
