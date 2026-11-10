# The "key estimate" M' ≤ C − k M² for 3D Navier–Stokes on T³: settled where it can be, open where it is open

Benjamin Stanley Frohman, 9 Nov 2026 (America/Chicago). Working directory: `/workspace/key-estimate-2026-11-09`.
Nothing here has been pushed or published.

## 0. Setting and the estimate

Navier–Stokes on T³ = (ℝ/2πℤ)³ with viscosity ν > 0, smooth divergence-free data u₀, vorticity ω = curl u, and
M(t) = ‖ω(·,t)‖_{L∞}. The draft's **key estimate** (`DraftRiccatiEstimate` in
`/workspace/left-side-lean-2026-11-09/FrohmanianTetherDraftAudit.lean`) is

  M'(t) ≤ C − k·M(t)²  on [0,T), with C ≥ 0, k > 0.

M is generally only Lipschitz, so we refute both the differentiable form (as in the Lean audit) and the weaker
form "upper right Dini derivative D⁺M(t) ≤ C − kM(t)²". Any of these forms forces M to be non-increasing whenever
M > √(C/k); in particular, if M(0) > √(C/k), M must start to decrease at t = 0.

## 1. Verdicts

| Variant | What C, k may depend on | Verdict |
|---|---|---|
| **V1** | nothing, or ν only (this is the draft's claim) | **Refuted.** Explicit trigonometric datum u₀ = A·U (§2). Exact, and the calculus and algebra are machine-checked in Lean. |
| **V2** | ν and the energy ‖u₀‖²_{L²}, in **any** way (arbitrary functions) | **Refuted.** Localized family (§3). Exact symbolic computation plus an interval-arithmetic (Arb) certificate of the global maximum. |
| V2′ | ν and ‖u₀‖_{L³} (scale-critical) | **Refuted** by the same family without the background term: ‖u₀‖_{L³} is exactly constant along it (§3.4). |
| **V3** | u₀ arbitrarily (e.g., via high Sobolev norms or ‖ω₀‖∞) | **Not refutable this way.** For each datum it is *equivalent* to global smoothness of that solution (§4). For all smooth data it is equivalent to global regularity on T³, i.e. the periodic Clay statement (B). **Open.** |

So the estimate as the draft uses it (constants depending at most on ν) is **false**. It also stays false if the
constants are allowed to depend on the energy. The only surviving version is a restatement of the open problem.

## 2. V1: explicit counterexample (trigonometric polynomial)

**Field.** U(x,y,z) = 3(−sin y, sin x, 0) + (−sin x cos z, 0, cos x sin z), and u₀ = A·U with A > 0.

Exact facts (sympy, `v1_trig_example.py` / `.log`; all re-proved in Lean, §5):
- div U = 0.
- Ω = curl U = (0, 2 sin x sin z, 3(cos x + cos y)).
- **Global maximum:** |Ω|² = 9(cos x + cos y)² + 4 sin²x sin²z ≤ 36, with |Ω(0)|² = 36.
  Elementary proof: (cos x + cos y)² ≤ 2cos²x + 2cos²y ≤ 2cos²x + 2, and 4 sin²x sin²z ≤ 4(1 − cos²x).
  So |Ω|² ≤ 22 + 14cos²x ≤ 36. Hence M(0) = ‖ω₀‖∞ = 6A, attained at x* = 0.
- At x* = 0: U(0) = 0, S(0) = diag(−1, 0, 1) (stretching along ξ = e_z = Ω(0)/|Ω(0)|), and ΔΩ(0) = (0, 0, −6).
- **The vorticity-equation right-hand side at (x,t) = (0,0)**, for u₀ = A·U, is
  (ω·∇)u − (u·∇)ω + νΔω = **(0, 0, 6A(A − ν))**.
  This is stretching 6A·A·1, advection 0 (since U(0) = 0), and diffusion νA·(−6).

**Argument.**
1. *(Classical, cited [K], [RRS] Ch. 6–7.)* For smooth data on T³ there is a unique solution, smooth on
   [0,T)×T³ including t = 0. So g(t) := ω₃(0,t) is C¹ on [0,T), and g'(0) is the third component of the
   right-hand side above: g'(0) = 6A(A − ν).
2. g(t) ≤ |ω(0,t)| ≤ M(t), and g(0) = 6A = M(0). (Using the component ω₃ avoids differentiating |·|.)
3. Lean lemma `draftRiccati_false_of_touch` (and `diniRiccati_false_of_touch` for the Dini form): if g touches
   M from below at 0 and g'(0⁺) > C − kM(0)², the estimate fails on every [0,T), T > 0.
4. Lean `amplitude_exists`: for every ν > 0, C ≥ 0 and k > 0 there is A > ν with
   6A(A − ν) > C − k(6A)². Explicitly, A = ν + 1 + |C|/k works.

Concretely, with ν = 1 and A = 3: M(0) = 18 and M increases at rate at least 36 at t = 0. Every fixed (C, k)
requires M to *decrease* once 18 > √(C/k), which this choice can always arrange. ∎

## 3. V2: constants depending on the energy (arbitrary functions of ν and ‖u₀‖_{L²})

Amplitude scaling alone cannot refute V2, because energy grows like A² and arbitrary C(E) can absorb that.
Periodic frequency scaling U(nx) keeps the energy fixed, but there viscosity wins (rate ∼ A²n² − νAn³).
The fix is **Navier–Stokes scaling of a localized field**: its energy goes to 0 while M₀² and the growth rate
both scale like λ⁴. A background field then pins the energy at any prescribed value.

### 3.1 The localized base field (on ℝ³, supported in the closed unit ball)
β(ρ) = exp(−3ρ/(1−ρ)) for ρ < 1 and 0 for ρ ≥ 1, which is C^∞ in ρ = |x|². Take
Ψ = β e_z + z β·(−y, x, 0) and u₁ = curl Ψ (smooth, compactly supported, divergence-free). It is a swirling
vortex plus an axisymmetric poloidal straining flow. Exact facts (`v2_symbolic.py` / `.log`; derivatives are
computed exactly as polynomial(x,y,z,t)·β with t = 1/(1−ρ)):
- div u₁ = 0. ω₁(0) = (0, 0, 12). u₁(0) = 0. ∇u₁(0) = [[−1,−6,0],[6,−1,0],[0,0,2]], so S₃₃(0) = 2.
  Δω₁(0) = (0, 0, −120).
- |ω₁|² is exactly invariant under rotations about the z-axis, and even in x and in z.
- **Global maximum certificate** (`v2_maxcert.py` / `.log`, python-flint 0.9.0 / Arb ball arithmetic, rigorous):
  max_{ℝ³} |ω₁|² = 144, attained only at the origin, so ‖ω₁‖∞ = 12. The proof covers [0,1]² in the (x,z) half-plane:
  - (I) On [−1/8, 1/8]², the interval Hessian is negative definite (592 boxes), so the function is strictly concave
    there with ∇ = 0 at 0. (The Hessian at 0 is diag(−1152, −576).)
  - (II) Every other box meeting ρ ≤ 19/20 has interval upper bound < 144 (4,345 evaluations).
  - (III) For 19/20 ≤ ρ < 1: |ω₁|² ≤ (Σ|coeff|)·t⁸·e^{−6(t−1)} with t ≥ 20, which gives ≤ 2.8·10⁻³⁵.

  Outside the unit ball the field is identically 0.

### 3.2 The family
Fix B = 10ν. For λ ≥ 1, place the scaled bump λB·u₁(λx) in a ball of radius 1/λ around 0 ∈ T³. Add a background
μ·u₂(x − p), where p = (π,π,π) and u₂ = curl(β(|x|²)e_z) is any fixed nonzero smooth compactly supported
divergence-free field on the unit ball. Its sup-vorticity M₂ < ∞ and energy E₂ > 0 are finite; their exact values
are not needed. The two supports are disjoint for all λ ≥ 1.
- Energy: ½‖u₀‖² = λ⁻¹B²E₁ + μ²E₂. Given **any** target E* > 0 and λ > B²E₁/E*, choose
  μ = √((E* − λ⁻¹B²E₁)/E₂) ≤ √(E*/E₂). Then the energy is exactly E* for all large λ.
- Sup-vorticity: M(0) = max(12Bλ², μM₂) = 120νλ² for λ large, attained at 0 (by §3.1).
- At (0,0), everything is local and the background vanishes near 0. Using the exact values above with
  ω = λ²Bω₁(λx):
  ∂ₜω₃(0,0) = (12λ²B)(2λ²B) − 0 + ν·λ⁴B·(−120) = λ⁴·24B(B − 5ν) = **1200ν²λ⁴**.
- As in §2, g(t) = ω₃(0,t) touches M from below at t = 0 with g'(0) = 1200ν²λ⁴. The Lean
  `localized_family_violation` lemma gives C − k(120νλ²)² < 1200ν²λ⁴ as soon as 1200ν²λ⁴ ≥ C. So for
  **every ν, E*, C = C(ν,E*) and k = k(ν,E*) > 0**, some smooth u₀ with energy exactly E* violates the
  estimate at t = 0. ∎

### 3.3 What this does not cover
Constants that may grow with a norm that blows up along the family, such as ‖u₀‖_{H^s} for s > 1/2,
‖u₀‖_{L^p} for p > 3, or ‖ω₀‖∞ itself, fall under V3.

### 3.4 V2′ (L³)
Without the background (μ = 0), ‖λB u₁(λ·)‖_{L³(T³)} = B‖u₁‖_{L³(ℝ³)} is exactly independent of λ. So
constants C(ν, ‖u₀‖_{L³}) and k(ν, ‖u₀‖_{L³}) are refuted by the same computation. For p < 3 the L^p norm
→ 0, which refutes constants that are locally bounded in that norm. Arbitrary dependence on an L^p norm with p < 3
needs the background trick with the L^p norm (additive over disjoint supports) in place of the energy. This is
the same argument, but it is not separately written out here.

## 4. V3: constants depending on u₀ arbitrarily. Equivalent to global regularity; OPEN

For a fixed smooth u₀ on T³, the following two statements are equivalent:
**(a)** the solution is global and smooth; **(b)** there are C ≥ 0 and k > 0 with D⁺M(t) ≤ C − kM(t)² for all t ≥ 0.
- (b) ⇒ (a): comparison for Dini derivatives gives M(t) ≤ max(M₀, √(C/k)), so ∫₀^T M < ∞ for every T,
  and BKM [BKM] rules out blow-up. (The Lean audit file already contains the conditional chain with BKM as a
  hypothesis.)
- (a) ⇒ (b): M(s) − M(t) ≤ (s−t)·sup_{[t,s]}‖∂ₜω‖∞, so D⁺M(t) ≤ ‖∂ₜω(t)‖∞. For a global smooth
  solution on T³, ∫₀^∞‖∇u‖₂² < ∞ gives a time t₀ with ‖∇u(t₀)‖₂ small. Small-data theory then gives decay of
  all H^s norms after t₀ [RRS §6.4], [FT], and continuity covers [0, t₀ + 1]. Hence sup_t ‖∂ₜω‖∞ < ∞ and
  sup_t M < ∞. Take k = 1 and C = sup D⁺M + sup M².

  *Cited ingredients, not re-proved here:* eventual smallness and decay of higher norms. (If ∫u₀ ≠ 0, also the
  Galilean reduction to mean zero.)

So V3 for all smooth data ⟺ every smooth periodic solution is global, which is Fefferman's Clay statement (B)
[F] (with period 2π instead of 1, equivalent by scaling). It is open. Nothing here proves or disproves it.

**Where the draft's derivation breaks**, now visible concretely: at a point where |ω| is maximal, the
vorticity equation gives d|ω|/dt = |ω|·(ξ·Sξ) + ν ξ·Δω. The stretching term can be positive (the eigenvalue
along ξ was +1 in §2 and +2 in §3). It is of size |ω|·|S| ~ M², with a *plus* sign. Nothing in the vorticity
equation forces a −kM² term. The draft's −kM² came from the tether, but in the earlier audit
(`draftRiccati_tether_iff_classical`) B(F,H) = 0 means the tether never acts on the flow.

## 5. Lean 4 (machine-checked part)

`lean/KeyEstimateRefutation.lean` (225 lines) is a new file. The audit project was **not** modified; it was used
read-only through `lake env`, with Lean 4.22.0 and the same Mathlib. Build: `cd /workspace/left-side-lean-2026-11-09 &&
lake env lean /workspace/key-estimate-2026-11-09/lean/KeyEstimateRefutation.lean`. It builds with 0 errors,
0 warnings, no `sorry` and no `axiom` declarations (log: `lean/build_final.log`). All 13 theorems depend only on
`[propext, Classical.choice, Quot.sound]`:

- `rightDeriv_le_of_touch`: a lower touching function's right derivative is ≤ M's.
- `draftRiccati_false_of_touch` uses `DraftRiccatiEstimate`, copied verbatim. `diniRiccati_false_of_touch` uses the Dini form.
- `div_free`, `w1_eq`, `w2_eq`, `w3_eq`: divergence and curl of A·U, computed with `deriv` on coordinate slices.
- `omega_sq_le`, `omega_at_origin`, `omega_norm_bound`: |ω| ≤ 6|A| everywhere, and ω(0) = (0, 0, 6A).
- `rhs_origin`: the vorticity-equation right-hand side at the origin is (0, 0, 6A(A−ν)). The Laplacian uses
  iterated `deriv`.
- `amplitude_exists`: for all ν, C and k > 0 there is A > ν with C − k(6A)² < 6A(A−ν).
- `localized_family_violation`: the scalar step of §3.

**Not in Lean** (cited or computed elsewhere):
- Navier–Stokes local well-posedness and smoothness up to t = 0, which identify g'(0) with the right-hand side.
- The V2 symbolic values and the Arb max certificate.
- Energy and support bookkeeping for the family.
- BKM, and the decay facts used in §4.

## 6. Numerical cross-check (NUMERICAL ONLY; not part of the proof)
`ns_check.py`: pseudo-spectral NS with 2/3 dealiasing and RK4, ν = 1.
- **V1** (A = 3, 64³, dt = 10⁻⁴): grid max|ω| rises from 18.000000 to 18.349 at t = 0.01 and 18.674 at t = 0.02.
  Over the first 0.002 the slope is 35.80, against the exact 36. The maximum stays at the origin.
- **Localized field** (B = 10, λ = 1): M₀ = 120 exactly.
  - At 128³ the grid M₀ is 119.918 and the initial slope 1514. This run is under-resolved because of the steep
    cutoff.
  - At 192³ (`ns_check_192.log`) the grid M₀ is 120.004 and the slope 1162, approaching the exact 1200. M rises
    monotonically over the computed window. The resolution trend is consistent with the exact value; no
    convergence claim is made beyond that.

## 7. References (verified to exist; cited for classical facts only)
- [BKM] J. T. Beale, T. Kato, A. Majda, *Remarks on the breakdown of smooth solutions for the 3-D Euler equations*,
  Comm. Math. Phys. 94 (1984) 61–66.
- [K] T. Kato, *Nonstationary flows of viscous and ideal fluids in ℝ³*, J. Funct. Anal. 9 (1972) 296–305.
- [RRS] J. C. Robinson, J. L. Rodrigo, W. Sadowski, *The Three-Dimensional Navier–Stokes Equations: Classical
  Theory*, Cambridge Stud. Adv. Math. 157, CUP 2016 (Ch. 6 strong solutions, §6.4 small data, Ch. 7 regularity,
  Ch. 12 vorticity/BKM).
- [MB] A. J. Majda, A. L. Bertozzi, *Vorticity and Incompressible Flow*, CUP 2002, §1.5. Vortex stretching:
  vorticity grows when aligned with positive strain eigenvectors. This is the mechanism used in §2–3; that ‖ω‖∞
  is not monotone is classical.
- [FT] C. Foias, R. Temam, *Gevrey class regularity for the solutions of the Navier–Stokes equations*,
  J. Funct. Anal. 87 (1989) 359–369.
- [F] C. L. Fefferman, *Existence and smoothness of the Navier–Stokes equation*, Clay Mathematics Institute
  official problem description (2000/2006).

## 8. Remaining open or uncited steps (explicit)
1. **V3 / Clay (B): open.** Not addressed, and no claim is made.
2. In §4 (a)⇒(b), the decay and eventual-smallness facts are cited rather than proved here. The equivalence is a
   remark, not part of the refutation.
3. §3.4: arbitrary dependence on an L^p norm with p < 3 is only sketched (same background trick).
4. Smoothness up to t = 0 and the pointwise vorticity equation at t = 0 are classical and cited, not formalized.
5. The Arb certificate depends on the correctness of python-flint/Arb and of the sympy-generated polynomials. The
   polynomial derivative rule is stated in `v2_symbolic.py`, and its outputs were cross-checked against direct sympy
   differentiation in `v2_explore.py` (grid maximum 144 at 0 for c = 3, ε = 1).
