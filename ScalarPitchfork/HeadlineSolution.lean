module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib
public import ScalarPitchfork

@[expose] public section

/-!
# Headline comparator Solution (untrusted)

Restates every theorem of `ScalarPitchfork.HeadlineChallenge` with the same name and
the same statement text, and proves it from the library declaration named in its
docstring: by `exact` where the Challenge only unfolds definitions, by supplying the
library witnesses (`branchRadius`, `BranchNhd`, `ampErr`, `branch`) for the existential
statements 1 and 5, and by assembling or splitting the `PitchforkJet` structure for
statements 8-10. Docstrings are copied from the Challenge.
-/

open Set Filter
open scoped Topology

namespace ScalarPitchforkHeadline.ScalarPitchfork

/-! ### 1. The two pitchfork branches -/

/-- **Pitchfork branches.** Under the remainder bounds (and continuity of `R` in `τ`),
there are a radius `ρ > 0`, an open neighbourhood `N` of `τ = 0`, a constant `K` and,
for each sign `σ = ±1`, a function `b σ`, continuous on `N` with `b σ 0 = 0`, such that:
`b σ τ = 0` when `τ β ≤ 0`; when `τ β > 0`, `z = b σ τ` is the unique zero of
`f(τ, ·)` with `σ z > 0` and `|z| ≤ ρ`, it satisfies `| |z| - √(α τ / β) | ≤ K |τ|`,
and `∂_z f(τ, z) β < 0`; and every zero `z ≠ 0` with `|z| ≤ ρ` and `τ ∈ N` has
`τ β > 0` and is `b 1 τ` or `b (-1) τ`.
Library: `ScalarPitchfork.pitchfork_branch_curves` (with `branch`, `branchRadius`,
`BranchNhd`, `ampErr` as witnesses). -/
theorem pitchfork_branch_curves (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ K : ℝ, ∃ b : ℝ → ℝ → ℝ,
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ b sgn 0 = 0 ∧
          (∀ tau ∈ N, tau * beta ≤ 0 → b sgn tau = 0) ∧
          (∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0 ∧
            |(|b sgn tau| - Real.sqrt (alpha * tau / beta))| ≤ K * |tau| ∧
            deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) (b sgn tau) * beta < 0)) ∧
      (∀ tau ∈ N, ∀ z : ℝ, z ≠ 0 → |z| ≤ ρ → alpha * tau * z - beta * z ^ 3 + R tau z = 0 →
        0 < tau * beta ∧ (z = b 1 tau ∨ z = b (-1) tau)) := by
  obtain ⟨hρ, hopen, hmem, hsgn, hcls⟩ :=
    _root_.ScalarPitchfork.pitchfork_branch_curves alpha beta C r R Rs halpha hbeta hC hr hr1
      hRval hRder hRs hRcont
  refine ⟨_root_.ScalarPitchfork.branchRadius alpha beta C r, hρ,
    {tau | _root_.ScalarPitchfork.BranchNhd alpha beta C r tau}, hopen, hmem,
    _root_.ScalarPitchfork.ampErr alpha beta C,
    fun sgn => _root_.ScalarPitchfork.branch alpha beta
      (_root_.ScalarPitchfork.branchRadius alpha beta C r) R sgn, fun sgn hs => ?_,
    fun tau htau z hz hzρ hroot => hcls tau z htau hz hzρ hroot⟩
  obtain ⟨hcont, hzero, -, hoff, hon⟩ := hsgn sgn hs
  refine ⟨hcont, hzero, fun tau htau hside => hoff tau htau hside, fun tau htau hside => ?_⟩
  obtain ⟨hu, ⟨hpos, hle, hroot⟩, hamp, hder⟩ := hon tau htau hside
  exact ⟨hu, hpos, hle, hroot, hamp, hder⟩

/-! ### 2. One signed zero at a fixed radius -/

/-- **Unique signed zero.** Under the remainder bounds there is `ρ > 0` such that for
all small `τ` with `τ β > 0` and each sign `σ = ±1`, `f(τ, ·)` has exactly one zero `z`
with `σ z > 0` and `|z| ≤ ρ`.
Library: `ScalarPitchfork.existsUnique_branchRoot_eventually` (verbatim). -/
theorem existsUnique_branchRoot_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta → ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0 := by
  exact _root_.ScalarPitchfork.existsUnique_branchRoot_eventually alpha beta C r R Rs halpha
    hbeta hC hr hr1 hRval hRder hRs

/-! ### 3. Existence with amplitude and stability -/

/-- **Existence of both branches.** Under the remainder bounds, for all small `τ` with
`τ β > 0` and each sign `σ = ±1` there is a zero `z` of `f(τ, ·)` with `σ z > 0`,
`| |z| - √(α τ / β) | ≤ K |τ|` for the explicit constant
`K = 2 α A (3|β|/(2α) + 1) / |β|²`, `A = C (2 (|β| + 2C)/α + 1)`, and `∂_z f(τ, z) β < 0`.
Library: `ScalarPitchfork.exists_branch_eventually` (with `pitchforkField`,
`absorbedConst`, `ampConst` unfolded). -/
theorem exists_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0 := by
  exact _root_.ScalarPitchfork.exists_branch_eventually alpha beta C r R Rs halpha hbeta hC hr
    hr1 hRval hRder hRs

/-! ### 4. Side and stability of every small zero -/

/-- **Side condition.** Under the remainder bounds, every zero `(τ, z)` of `f` near
`(0, 0)` with `z ≠ 0` has `τ β > 0` and `∂_z f(τ, z) β < 0`.
Library: `ScalarPitchfork.branch_side_eventually` (with `pitchforkField` unfolded). -/
theorem branch_side_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), p.2 ≠ 0 →
      alpha * p.1 * p.2 - beta * p.2 ^ 3 + R p.1 p.2 = 0 →
        0 < p.1 * beta ∧
          deriv (fun z => alpha * p.1 * z - beta * z ^ 3 + R p.1 z) p.2 * beta < 0 := by
  exact _root_.ScalarPitchfork.branch_side_eventually alpha beta C r R Rs halpha hbeta hC hr hr1
    hRval hRder hRs

/-! ### 5. Classification of small zeros -/

/-- **At most one small zero of each sign.** Under the remainder bounds there is
`ρ > 0` such that, for all small `τ`, two zeros `z₁, z₂` of `f(τ, ·)` of the same
strict sign with `|z₁|, |z₂| ≤ ρ` are equal. With statement 1, the small nonzero
zeros are exactly the two branch values.
Library: `ScalarPitchfork.small_zero_eq_branch` (both zeros equal the branch value
of their sign). -/
theorem small_zero_eq_branch (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ tau in 𝓝 (0 : ℝ), ∀ z₁ z₂ : ℝ, 0 < z₁ * z₂ → |z₁| ≤ ρ → |z₂| ≤ ρ →
      alpha * tau * z₁ - beta * z₁ ^ 3 + R tau z₁ = 0 →
      alpha * tau * z₂ - beta * z₂ ^ 3 + R tau z₂ = 0 → z₁ = z₂ := by
  refine ⟨_root_.ScalarPitchfork.branchRadius alpha beta C r,
    _root_.ScalarPitchfork.branchRadius_pos alpha beta C r halpha hbeta hC hr, ?_⟩
  filter_upwards [_root_.ScalarPitchfork.branchNhd_mem_nhds alpha beta C r halpha hbeta hC hr]
    with tau hsmall
  intro z₁ z₂ hprod h₁ h₂ hr₁ hr₂
  have hz₁ : z₁ ≠ 0 := by rintro rfl; simp at hprod
  have hz₂ : z₂ ≠ 0 := by rintro rfl; simp at hprod
  obtain ⟨hside, hb₁⟩ := _root_.ScalarPitchfork.small_zero_eq_branch alpha beta C r tau z₁ R Rs
    halpha hbeta hC hr hr1 hRval hRder hRs hsmall hz₁ h₁ hr₁
  obtain ⟨-, hb₂⟩ := _root_.ScalarPitchfork.small_zero_eq_branch alpha beta C r tau z₂ R Rs
    halpha hbeta hC hr hr1 hRval hRder hRs hsmall hz₂ h₂ hr₂
  have hp := (_root_.ScalarPitchfork.branch_spec alpha beta C r tau R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside 1 (Or.inl rfl)).1.1
  have hn := (_root_.ScalarPitchfork.branch_spec alpha beta C r tau R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside (-1) (Or.inr rfl)).1.1
  rcases hb₁ with e₁ | e₁ <;> rcases hb₂ with e₂ | e₂ <;> rw [e₁, e₂] at hprod ⊢
  · nlinarith
  · nlinarith

/-! ### 6. Exchange of stability on the exact cubic -/

/-- **Derivative at a nontrivial equilibrium.** If `A ≠ 0` and `α τ A - β A³ = 0` (with
`β ≠ 0`), then `∂_A (α τ A - β A³) = -2 α τ` at `A`.
Library: `ScalarPitchfork.deriv_cubicField_at_branch` (with `cubicField` unfolded). -/
theorem deriv_cubicField_at_branch (alpha beta tau A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    deriv (fun A => alpha * tau * A - beta * A ^ 3) A = -2 * alpha * tau := by
  exact _root_.ScalarPitchfork.deriv_cubicField_at_branch alpha beta tau A hbeta hA hroot

/-! ### 7. Square-root amplitude error -/

/-- **Amplitude error.** If `z ≠ 0`, `α τ - β z² + e = 0`, `α τ / β ≥ 0` and
`|e| ≤ C |z|³`, then `| |z| - √(α τ / β) | ≤ C z² / |β|`.
Library: `ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder` (verbatim). -/
theorem abs_sub_sqrt_le_of_cubic_remainder (alpha beta tau z e C : ℝ)
    (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (ht : 0 ≤ alpha * tau / beta) (herr : |e| ≤ C * |z| ^ 3) :
    |(|z| - Real.sqrt (alpha * tau / beta))| ≤ C * z ^ 2 / |beta| := by
  exact _root_.ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder alpha beta tau z e C hbeta hs
    hroot ht herr

/-! ### 8-10. Remainder bounds from jets at the origin -/

/-- **Remainder bounds from jets.** Let `R` be `C⁴` on an open `U ⊇ closedBall 0 r`
(`0 < r ≤ 1`), vanish on the axis `z = 0`, and have zero jets `∂_z, ∂_τ∂_z, ∂_z²,
∂_τ∂_z², ∂_z³` at the origin. Then there is `C ≥ 0` such that `R` satisfies the
remainder bounds of statements 1-5 on the box with `R_z = D R (τ, z) (0, 1)`, and
`R` is continuous in `τ`.
Library: `ScalarPitchfork.remainderBounds_of_jet` (with `PitchforkJet`, `jetRs`,
`eTau = (1, 0)`, `eZ = (0, 1)` unfolded). -/
theorem remainderBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        HasDerivAt (R e) (iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]) z) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        |iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]| ≤
          C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) ∧
      (∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) := by
  exact _root_.ScalarPitchfork.remainderBounds_of_jet R U r
    ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩

/-- **Stronger bound iff the axis condition.** Under the hypotheses of statement 8,
`R` satisfies the stronger bound `|R(τ, z)| ≤ C (z² τ² + |z|³ |τ| + z⁴)` on the box
for some `C` if and only if `∂_z R(τ, 0) = 0` for all `|τ| ≤ r`.
Library: `ScalarPitchfork.strongBound_iff_axis` (with `PitchforkJet`, `jetRs` unfolded). -/
theorem strongBound_iff_axis (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    (∃ C, ∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ↔
      ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 (Function.uncurry R) (e, 0) ![(0, 1)] = 0 := by
  exact _root_.ScalarPitchfork.strongBound_iff_axis R U r
    ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩

/-- **Jets at the origin do not give the stronger bound.** It is not true that every `R`
satisfying the hypotheses of statement 8 satisfies the stronger bound
`|R(τ, z)| ≤ C (z² τ² + |z|³ |τ| + z⁴)` for some `C`; `R(τ, z) = τ² z` is a counterexample.
Library: `ScalarPitchfork.jet_not_sufficient_for_strongBound` (with `PitchforkJet`
unfolded). -/
theorem jet_not_sufficient_for_strongBound :
    ¬ ∀ (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ),
      IsOpen U → ContDiffOn ℝ 4 (Function.uncurry R) U → 0 < r → r ≤ 1 →
      Metric.closedBall (0 : ℝ × ℝ) r ⊆ U → (∀ e, |e| ≤ r → R e 0 = 0) →
      iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0 →
      iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0 →
      iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0 →
      iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0 →
      iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0 →
      ∃ C, ∀ e z, |e| ≤ r → |z| ≤ r →
        |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
  intro hall
  exact _root_.ScalarPitchfork.jet_not_sufficient_for_strongBound fun R U r h =>
    hall R U r h.isOpen h.smooth h.r_pos h.r_le_one h.box_sub h.trivial h.jet_z h.jet_tau_z
      h.jet_zz h.jet_tau_zz h.jet_zzz

end ScalarPitchforkHeadline.ScalarPitchfork

namespace ScalarPitchforkHeadline.ScalarPitchfork.Global

/-! ### 11. A non-compact component is unbounded in the parameter -/

/-- **Unbounded parameter.** Let `C ⊆ V ⊆ ℝ × E` be relatively closed in `V`, with
`C ⊆ closure S ⊆ V`, where every bounded-parameter slice `S ∩ {λ ≤ X}` has compact
closure. If `C` is not compact, then `C` contains points with arbitrarily large
parameter, and the supremum of its parameters in `EReal` is `⊤`.
Library: `ScalarPitchfork.Global.sSup_param_eq_top` (verbatim). -/
theorem sSup_param_eq_top {E : Type*} [TopologicalSpace E] {C S V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  exact _root_.ScalarPitchfork.Global.sSup_param_eq_top hRelClosed hCV hCS hAdmissible
    hPrecompact hNC

/-! ### 12. The one-sided component is closed -/

/-- **Closed one-sided component.** Let `S` be closed, `base ∈ S`, and let `A` be
relatively open in the component `K` of `base` in `S`. For `selector ∈ K \ A`, the
component of `selector` in `K \ A` is closed.
Library: `ScalarPitchfork.Global.selectedComponent_isClosed` (with `parentComponent`,
`unilateralRemainder`, `selectedComponent` unfolded). -/
theorem selectedComponent_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base selector : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen (((↑) : connectedComponentIn solutionClosure base → X) ⁻¹' removedArc))
    (hSelectorInRemainder :
      selector ∈ connectedComponentIn solutionClosure base \ removedArc) :
    IsClosed (connectedComponentIn
      (connectedComponentIn solutionClosure base \ removedArc) selector) := by
  exact _root_.ScalarPitchfork.Global.selectedComponent_isClosed hSolutionClosed hBase
    hRemovedRelOpen hSelectorInRemainder

end ScalarPitchforkHeadline.ScalarPitchfork.Global
