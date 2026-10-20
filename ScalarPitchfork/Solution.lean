module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib
public import ScalarPitchfork

@[expose] public section

/-!
# Comparator Solution (untrusted)

Restates every theorem of `ScalarPitchfork.Challenge` with the same name and the same
statement text, and proves it from the library declaration named in its docstring: by
`exact` where the Challenge only unfolds definitions, by assembling or splitting the
`PitchforkJet` structure where the Challenge lists its fields as hypotheses, and by
supplying the library witnesses (`branchRadius`, `BranchNhd`, `ampErr`, `branch`) for the
existential statements about the branch functions. Docstrings are copied from the
Challenge.
-/

/-! ## Part I: the headline results -/

open Set Filter
open scoped Topology

namespace ScalarPitchforkAudit.ScalarPitchfork

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

end ScalarPitchforkAudit.ScalarPitchfork

namespace ScalarPitchforkAudit.ScalarPitchfork.Global

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

end ScalarPitchforkAudit.ScalarPitchfork.Global

/-! ## Part II: further reusable results of the library -/

namespace ScalarPitchforkAudit.ScalarPitchfork

/-! ### 13-16. The stronger remainder bounds -/

/-- **Stronger bounds from jets and the axis condition.** Under the hypotheses of
statement 8 and the axis condition `∂_z R(τ, 0) = 0` for `|τ| ≤ r`, there is `C ≥ 0` with
`|R(τ, z)| ≤ C (z² τ² + |z|³ |τ| + z⁴)` and `|∂_z R(τ, z)| ≤ C (|z| τ² + z² |τ| + |z|³)`
on the box, where `∂_z R(τ, z) = D R (τ, z) (0, 1)`.
Library: `ScalarPitchfork.strongBounds_of_jet` (with `PitchforkJet`, `jetRs`, `eTau`,
`eZ` unfolded). -/
theorem strongBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 (Function.uncurry R) (e, 0) ![(0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        |iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]| ≤
          C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) := by
  exact _root_.ScalarPitchfork.strongBounds_of_jet R U r
    ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩ hlin

/-- **Existence of both branches under the stronger bounds.** If
`|R(τ, z)| ≤ C (z² τ² + |z|³ |τ| + z⁴)`, `∂_z R = R_z` and
`|R_z(τ, z)| ≤ C (|z| τ² + z² |τ| + |z|³)` on the box, then the conclusion of
statement 3 holds, with the same explicit constant.
Library: `ScalarPitchfork.branch_eventually_of_strongBound` (with `pitchforkField`,
`absorbedConst`, `ampConst` unfolded). -/
theorem branch_eventually_of_strongBound (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0 := by
  exact _root_.ScalarPitchfork.branch_eventually_of_strongBound alpha beta C r R Rs halpha hbeta
    hC hr hr1 hRval hRder hRs

/-- **Branch curves under the stronger bounds.** Under the stronger bounds of the
previous statement and continuity of `R` in `τ`, there are a radius `ρ > 0`, an open
neighbourhood `N` of `τ = 0` and, for each sign `σ = ±1`, a function `b σ`, continuous on
`N` with `b σ τ → 0` as `τ → 0`, such that for `τ ∈ N` with `τ β > 0`, `f(τ, ·)` has
exactly one zero `z` with `σ z > 0` and `|z| ≤ ρ`, and `b σ τ` is such a zero.
Library: `ScalarPitchfork.branch_curves_of_strongBound` (with `branch`, `branchRadius`,
`BranchNhd` as witnesses, `BranchRoot` and `pitchforkField` unfolded; the clause that
`b σ τ` is the zero is the defining property of the library's `branch`, from
`ScalarPitchfork.branch_spec`). -/
theorem branch_curves_of_strongBound (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ b : ℝ → ℝ → ℝ,
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ Tendsto (b sgn) (𝓝 0) (𝓝 0) ∧
          ∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0 := by
  have hRval' : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := fun e z he hz =>
    _root_.ScalarPitchfork.value_bound_weak_of_strongBound e z (R e z) C hC (hz.trans hr1)
      (hRval e z he hz)
  have hRs' : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) := fun e z he hz =>
    _root_.ScalarPitchfork.deriv_bound_weak_of_strongBound e z (Rs e z) C hC (hz.trans hr1)
      (hRs e z he hz)
  refine ⟨_root_.ScalarPitchfork.branchRadius alpha beta C r,
    _root_.ScalarPitchfork.branchRadius_pos alpha beta C r halpha hbeta hC hr,
    {tau | _root_.ScalarPitchfork.BranchNhd alpha beta C r tau},
    _root_.ScalarPitchfork.isOpen_branchNhd alpha beta C r,
    _root_.ScalarPitchfork.branchNhd_mem_nhds alpha beta C r halpha hbeta hC hr,
    fun sgn => _root_.ScalarPitchfork.branch alpha beta
      (_root_.ScalarPitchfork.branchRadius alpha beta C r) R sgn, fun sgn hs => ?_⟩
  obtain ⟨hcont, htend, huniq⟩ :=
    _root_.ScalarPitchfork.branch_curves_of_strongBound alpha beta C r R Rs halpha hbeta hC hr
      hr1 hRval hRder hRs hRcont sgn hs
  refine ⟨hcont, htend, fun tau htau hside => ⟨huniq tau htau hside, ?_⟩⟩
  exact (_root_.ScalarPitchfork.branch_spec alpha beta C r tau R Rs halpha hbeta hC hr hr1
    hRval' hRder hRs' htau hside sgn hs).1

/-- **Zero-level conclusions under the stronger bounds.** Let `z ≠ 0`, `|z| ≤ 1`,
`|τ| ≤ 1`, `2 C |τ| ≤ α`, `α τ z - β z³ + R = 0`, `d = α τ - 3 β z² + R_s`,
`|R| ≤ C (z² τ² + |z|³ |τ| + z⁴)`, `|R_s| ≤ C (|z| τ² + z² |τ| + |z|³)` and
`A (|τ| + |z|) ≤ |β| / 2` with `A = C (2 (|β| + 2C)/α + 1)`. Then `τ β > 0`, `d β < 0`
and `| |z| - √(α τ / β) | ≤ 2 α A (3|β|/(2α) + 1) / |β|² · |τ|`.
Library: `ScalarPitchfork.equilibrium_core_of_strongBound` (with `absorbedConst`,
`ampConst` unfolded). -/
theorem equilibrium_core_of_strongBound (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (z ^ 2 * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (|z| * tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : C * (2 * (|beta| + 2 * C) / alpha + 1) * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  exact _root_.ScalarPitchfork.equilibrium_core_of_strongBound alpha beta tau z R Rs ds C halpha
    hbeta hs hC hs1 heta1 hetaC hroot hderiv hR hRs hrectangle

/-! ### 17-22. Zero-level analysis and the jet route -/

/-- **Axis condition from the linearization.** Let `f(τ, z)` be a field whose remainder
`R(τ, z) = f(τ, z) - α τ z + β z³` satisfies the hypotheses of statement 8, and let
`∂_z f(τ, 0) = α τ` for `|τ| ≤ r`. Then `∂_z R(τ, 0) = 0` for `|τ| ≤ r`.
Library: `ScalarPitchfork.axis_of_linearization` (with `remainderOf`, `PitchforkJet`,
`AxisLinearization`, `jetRs`, `eTau`, `eZ` unfolded). -/
theorem axis_of_linearization (alpha beta : ℝ) (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U)
    (hsmooth : ContDiffOn ℝ 4
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → f e 0 - alpha * e * 0 + beta * 0 ^ 3 = 0)
    (hz : iteratedFDeriv ℝ 1
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(0, 1), (0, 1), (0, 1)] = 0)
    (hlin : ∀ e, |e| ≤ r → HasDerivAt (f e) (alpha * e) 0) :
    ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) (e, 0) ![(0, 1)] = 0 := by
  exact _root_.ScalarPitchfork.axis_of_linearization alpha beta f U r
    ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩ hlin

/-- **Zero-level conclusions for the perturbed cubic.** Let `z ≠ 0`, `|z| ≤ 1`,
`α τ z - β z³ + R = 0`, `d = α τ - 3 β z² + R_s`, `|R| ≤ C (|τ| |z|³ + |z|⁴)`,
`|R_s| ≤ C (|τ| z² + |z|³)` and `C (|τ| + |z|) ≤ |β| / 2`. Then `τ β > 0`, `d β < 0` and
`| |z| - √(α τ / β) | ≤ 2 α C (3|β|/(2α) + 1) / |β|² · |τ|`.
Library: `ScalarPitchfork.perturbed_equilibrium_core` (verbatim). -/
theorem perturbed_equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|tau| * |z| ^ 3 + |z| ^ 4))
    (hRs : |Rs| ≤ C * (|tau| * z ^ 2 + |z| ^ 3))
    (hrectangle : C * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  exact _root_.ScalarPitchfork.perturbed_equilibrium_core alpha beta tau z R Rs ds C halpha hbeta
    hs hC hs1 hroot hderiv hR hRs hrectangle

/-- **Zero-level conclusions under the remainder bounds.** Let `z ≠ 0`, `|z| ≤ 1`,
`|τ| ≤ 1`, `2 C |τ| ≤ α`, `α τ z - β z³ + R = 0`, `d = α τ - 3 β z² + R_s`,
`|R| ≤ C (|z| τ² + |z|³ |τ| + z⁴)`, `|R_s| ≤ C (τ² + z² |τ| + |z|³)` and
`A (|τ| + |z|) ≤ |β| / 2` with `A = C (2 (|β| + 2C)/α + 1)`. Then `τ β > 0`, `d β < 0`
and `| |z| - √(α τ / β) | ≤ 2 α A (3|β|/(2α) + 1) / |β|² · |τ|`.
Library: `ScalarPitchfork.equilibrium_core` (with `absorbedConst`, `ampConst`
unfolded). -/
theorem equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : C * (2 * (|beta| + 2 * C) / alpha + 1) * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  exact _root_.ScalarPitchfork.equilibrium_core alpha beta tau z R Rs ds C halpha hbeta hs hC
    hs1 heta1 hetaC hroot hderiv hR hRs hrectangle

/-- **Pitchfork branches from jets.** If `R` satisfies the hypotheses of statement 8,
then the conclusion of statement 1 holds for `f(τ, z) = α τ z - β z³ + R(τ, z)`, with,
in addition, `b σ τ → 0` as `τ → 0`.
Library: `ScalarPitchfork.pitchfork_branch_curves_of_jet` (with `PitchforkJet` unfolded
and `branch`, `branchRadius`, `BranchNhd`, `ampErr` as witnesses; the library's remainder
constant `C` occurs only through these witnesses and is dropped). -/
theorem pitchfork_branch_curves_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ))
    (r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ K : ℝ, ∃ b : ℝ → ℝ → ℝ,
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ b sgn 0 = 0 ∧ Tendsto (b sgn) (𝓝 0) (𝓝 0) ∧
          (∀ tau ∈ N, tau * beta ≤ 0 → b sgn tau = 0) ∧
          (∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0 ∧
            |(|b sgn tau| - Real.sqrt (alpha * tau / beta))| ≤ K * |tau| ∧
            deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) (b sgn tau) * beta < 0)) ∧
      (∀ tau ∈ N, ∀ z : ℝ, z ≠ 0 → |z| ≤ ρ → alpha * tau * z - beta * z ^ 3 + R tau z = 0 →
        0 < tau * beta ∧ (z = b 1 tau ∨ z = b (-1) tau)) := by
  obtain ⟨C, -, hρ, hopen, hmem, hsgn, hcls⟩ :=
    _root_.ScalarPitchfork.pitchfork_branch_curves_of_jet alpha beta R U r halpha hbeta
      ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩
  refine ⟨_root_.ScalarPitchfork.branchRadius alpha beta C r, hρ,
    {tau | _root_.ScalarPitchfork.BranchNhd alpha beta C r tau}, hopen, hmem,
    _root_.ScalarPitchfork.ampErr alpha beta C,
    fun sgn => _root_.ScalarPitchfork.branch alpha beta
      (_root_.ScalarPitchfork.branchRadius alpha beta C r) R sgn, fun sgn hs => ?_,
    fun tau htau z hz hzρ hroot => hcls tau z htau hz hzρ hroot⟩
  obtain ⟨hcont, hzero, htend, hoff, hon⟩ := hsgn sgn hs
  refine ⟨hcont, hzero, htend, fun tau htau hside => hoff tau htau hside,
    fun tau htau hside => ?_⟩
  obtain ⟨hu, ⟨hpos, hle, hroot⟩, hamp, hder⟩ := hon tau htau hside
  exact ⟨hu, hpos, hle, hroot, hamp, hder⟩

/-- **Existence of both branches from jets.** If `R` satisfies the hypotheses of
statement 8, there is `C ≥ 0` such that the conclusion of statement 3 holds with
`R_z = D R (τ, z) (0, 1)` and the explicit constant of statement 3 for this `C`.
Library: `ScalarPitchfork.exists_branch_eventually_of_jet` (with `PitchforkJet`,
`pitchforkField`, `absorbedConst`, `ampConst` unfolded). -/
theorem exists_branch_eventually_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ))
    (r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0 := by
  exact _root_.ScalarPitchfork.exists_branch_eventually_of_jet alpha beta R U r halpha hbeta
    ⟨hU, hsmooth, hr, hr1, hbox, haxis, hz, htz, hzz, htzz, hzzz⟩

/-- **A derivative killed by a quadratic bound.** If `φ` has derivative `d` at `0` and
`|φ z| ≤ K z²` for `|z| ≤ δ` (`δ > 0`), then `d = 0`.
Library: `ScalarPitchfork.deriv_zero_of_sq_bound` (verbatim). -/
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ z, |z| ≤ δ → |φ z| ≤ K * z ^ 2) : d = 0 := by
  exact _root_.ScalarPitchfork.deriv_zero_of_sq_bound φ d K δ hδ hd hb

/-! ### 23-24. The exact cubic and existence at one parameter -/

/-- **Nonzero zeros of the exact cubic.** If `α > 0`, `β ≠ 0`, `A ≠ 0` and
`α τ A - β A³ = 0`, then `A = √(α τ / β)` or `A = -√(α τ / β)`.
Library: `ScalarPitchfork.nonzero_equilibrium_eq_branch` (with `cubicField` unfolded). -/
theorem nonzero_equilibrium_eq_branch (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    A = Real.sqrt (alpha * tau / beta) ∨ A = -Real.sqrt (alpha * tau / beta) := by
  exact _root_.ScalarPitchfork.nonzero_equilibrium_eq_branch alpha beta tau A halpha hbeta hA
    hroot

/-- **A positive zero at one parameter.** Let `α > 0`, `τ β > 0`, `C ≥ 0`, `R`
continuous on `[√(α τ/(2β)), √(2 α τ/β)]` with `|R z| ≤ C (|z| τ² + |z|³ |τ| + z⁴)` for
`0 < z`, `z² ≤ 2 α τ / β`, and `C (|τ| + 2 α τ/β + 2 α √(2 α τ/β) / |β|) < α / 2`. Then
there is `z > 0` with `α τ / (2β) ≤ z² ≤ 2 α τ / β` and `α τ z - β z³ + R z = 0`.
Library: `ScalarPitchfork.exists_pos_equilibrium` (verbatim). -/
theorem exists_pos_equilibrium (alpha beta tau C : ℝ) (R : ℝ → ℝ)
    (halpha : 0 < alpha) (hside : 0 < tau * beta) (hC : 0 ≤ C)
    (hcont : ContinuousOn R
      (Set.Icc (Real.sqrt (alpha * tau / beta / 2)) (Real.sqrt (2 * (alpha * tau / beta)))))
    (hR : ∀ z, 0 < z → z ^ 2 ≤ 2 * (alpha * tau / beta) →
      |R z| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hsmall : C * (|tau| + 2 * (alpha * tau / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2) :
    ∃ z, 0 < z ∧ alpha * tau / beta / 2 ≤ z ^ 2 ∧ z ^ 2 ≤ 2 * (alpha * tau / beta) ∧
      alpha * tau * z - beta * z ^ 3 + R z = 0 := by
  exact _root_.ScalarPitchfork.exists_pos_equilibrium alpha beta tau C R halpha hside hC hcont
    hR hsmall

end ScalarPitchforkAudit.ScalarPitchfork

namespace ScalarPitchforkAudit.ScalarPitchfork.Global

/-! ### 25-31. Global alternatives and connectedness propagation -/

/-- **Global unboundedness of a monotone branch.** Let `C ⊆ ℝ × E` satisfy the global
alternatives (`C` not compact, or `(λ, u*) ∈ C` for some `λ ≠ λ*`, or
`(λ, u* + w) ∈ C` for some `w ∈ W \ {0}`), let every point of `C` other than `(λ*, u*)`
have a strictly monotone profile on `[0, L]` (`L > 0`, profiles continuous, `u*` constant),
let `φ` pair positively with every continuous strictly decreasing profile and be
orthogonal to the profiles of `W`, and let `C` satisfy the hypotheses of statement 11
except non-compactness. Then the second and third alternatives fail, `C` is not compact,
`C` has arbitrarily large parameters and the supremum of its parameters is `⊤`.
Library: `ScalarPitchfork.Global.global_unbounded_of_monotone` (with
`GlobalAlternatives`, `AltNoncompact`, `AltOtherTrivial`, `AltComplement` unfolded). -/
theorem global_unbounded_of_monotone {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C S V : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hL : 0 < L)
    (hAlt : ¬ IsCompact C ∨ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∨
      ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C)
    (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hφ : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 L) → StrictAntiOn g (Icc 0 L) →
      0 < ∫ x in (0 : ℝ)..L, g x * φ x)
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * φ x = 0)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L))
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar}))) :
    ¬ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∧
      ¬ (∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C) ∧
      ¬ IsCompact C ∧ (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  exact _root_.ScalarPitchfork.Global.global_unbounded_of_monotone hL hAlt hConst hCont hφ hW
    hMono hRelClosed hCV hCS hAdmissible hPrecompact

/-- **The complement alternative fails for a monotone branch.** Under the profile
hypotheses of statement 25, no point `(λ, u* + w)` with `w ∈ W \ {0}` lies in `C`.
Library: `ScalarPitchfork.Global.not_altComplement` (with `AltComplement` unfolded). -/
theorem not_altComplement {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hφ : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 L) → StrictAntiOn g (Icc 0 L) →
      0 < ∫ x in (0 : ℝ)..L, g x * φ x)
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * φ x = 0)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C := by
  exact _root_.ScalarPitchfork.Global.not_altComplement hConst hCont hφ hW hMono

/-- **The other-trivial alternative fails for a monotone branch.** If `L > 0`, the
profile of `u*` is constant and every point of `C` other than `(λ*, u*)` has a strictly
monotone profile on `[0, L]`, then `(λ, u*) ∉ C` for every `λ ≠ λ*`.
Library: `ScalarPitchfork.Global.not_altOtherTrivial` (with `AltOtherTrivial`
unfolded). -/
theorem not_altOtherTrivial {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C := by
  exact _root_.ScalarPitchfork.Global.not_altOtherTrivial hL hConst hMono

/-- **Alternative elimination.** If `C` satisfies the global alternatives and the second
and third alternatives fail, then `C` is not compact.
Library: `ScalarPitchfork.Global.not_isCompact_of_alternatives` (with
`GlobalAlternatives`, `AltNoncompact`, `AltOtherTrivial`, `AltComplement` unfolded). -/
theorem not_isCompact_of_alternatives {E : Type*} [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {lamStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : ¬ IsCompact C ∨ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∨
      ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C)
    (hNotII : ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C)
    (hNotIII : ¬ ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C) :
    ¬ IsCompact C := by
  exact _root_.ScalarPitchfork.Global.not_isCompact_of_alternatives hAlt hNotII hNotIII

/-- **Compact bounded-parameter slices.** If `C` is closed, `C ⊆ closure S`, and every
`S ∩ {λ ≤ X}` has compact closure, then every slice `C ∩ {λ ≤ X}` is compact.
Library: `ScalarPitchfork.Global.isCompact_slice` (verbatim). -/
theorem isCompact_slice {E : Type*} [TopologicalSpace E] {C S : Set (ℝ × E)}
    (hClosed : IsClosed C) (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar}) := by
  exact _root_.ScalarPitchfork.Global.isCompact_slice hClosed hCS hPrecompact Xbar

/-- **Connectedness propagation.** If `C` is preconnected, `p* ∈ C ∩ M`, and
`C ∩ M` is relatively clopen in `C`, then `C ⊆ M`.
Library: `ScalarPitchfork.Global.subset_of_relClopen` (verbatim). -/
theorem subset_of_relClopen {E : Type*} [TopologicalSpace E] {C M : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C) (hStarM : pStar ∈ M)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' M)) :
    C ⊆ M := by
  exact _root_.ScalarPitchfork.Global.subset_of_relClopen hConn hStar hStarM hClopen

/-- **Strict decrease propagates along a component.** If `C` is preconnected, `p* ∈ C`,
and the set of points of `C` that are `p*` or have a strictly decreasing profile on
`[0, L]` is relatively clopen in `C`, then every `p ∈ C` other than `p*` has a strictly
decreasing profile on `[0, L]`.
Library: `ScalarPitchfork.Global.strictAntiOn_of_relClopen` (with `DecreasingLocus`
unfolded). -/
theorem strictAntiOn_of_relClopen {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹'
      {p | p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)})) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) := by
  exact _root_.ScalarPitchfork.Global.strictAntiOn_of_relClopen prof L hConn hStar hClopen

/-! ### 32-40. Closedness of the one-sided component -/

/-- **Components of closed sets are closed.** If `F` is closed and `x ∈ F`, the
connected component of `x` in `F` is closed.
Library: `ScalarPitchfork.Global.isClosed_connectedComponentIn_of_isClosed`
(verbatim). -/
theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X]
    {F : Set X} {x : X} (hF : IsClosed F) (hx : x ∈ F) :
    IsClosed (connectedComponentIn F x) := by
  exact _root_.ScalarPitchfork.Global.isClosed_connectedComponentIn_of_isClosed hF hx

/-- **Removing a relatively open set from a closed set.** If `P` is closed and `A ∩ P`
is relatively open in `P`, then `P \ A` is closed.
Library: `ScalarPitchfork.Global.isClosed_sdiff_of_isOpen_preimage` (verbatim). -/
theorem isClosed_sdiff_of_isOpen_preimage {X : Type*} [TopologicalSpace X]
    {parent removed : Set X} (hParent : IsClosed parent)
    (hRemoved : IsOpen (((↑) : parent → X) ⁻¹' removed)) :
    IsClosed (parent \ removed) := by
  exact _root_.ScalarPitchfork.Global.isClosed_sdiff_of_isOpen_preimage hParent hRemoved

/-- **Closed parent component.** If `S` is closed and `base ∈ S`, the component of
`base` in `S` is closed.
Library: `ScalarPitchfork.Global.parentComponent_isClosed` (with `parentComponent`
unfolded). -/
theorem parentComponent_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure) :
    IsClosed (connectedComponentIn solutionClosure base) := by
  exact _root_.ScalarPitchfork.Global.parentComponent_isClosed hSolutionClosed hBase

/-- **Closed unilateral remainder.** If `S` is closed, `base ∈ S`, and `A` is relatively
open in the component `K` of `base` in `S`, then `K \ A` is closed.
Library: `ScalarPitchfork.Global.unilateralRemainder_isClosed` (with `parentComponent`,
`unilateralRemainder` unfolded). -/
theorem unilateralRemainder_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen (((↑) : connectedComponentIn solutionClosure base → X) ⁻¹' removedArc)) :
    IsClosed (connectedComponentIn solutionClosure base \ removedArc) := by
  exact _root_.ScalarPitchfork.Global.unilateralRemainder_isClosed hSolutionClosed hBase
    hRemovedRelOpen

/-- **The retained arc lies in the parent component.** If `{base} ∪ A'` is connected and
contained in `S`, it is contained in the component of `base` in `S`.
Library: `ScalarPitchfork.Global.retainedWithBase_subset_parentComponent` (with
`parentComponent` unfolded). -/
theorem retainedWithBase_subset_parentComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base := by
  exact _root_.ScalarPitchfork.Global.retainedWithBase_subset_parentComponent
    hRetainedConnected hRetainedInSolution

/-- **The retained arc lies in the unilateral remainder.** If `{base} ∪ A'` is
connected, contained in `S` and disjoint from `A`, it is contained in `K \ A`, where `K`
is the component of `base` in `S`.
Library: `ScalarPitchfork.Global.retainedWithBase_subset_unilateralRemainder` (with
`parentComponent`, `unilateralRemainder` unfolded). -/
theorem retainedWithBase_subset_unilateralRemainder {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base \ removedArc := by
  exact _root_.ScalarPitchfork.Global.retainedWithBase_subset_unilateralRemainder
    hRetainedConnected hRetainedInSolution hAvoidRemoved

/-- **The retained arc lies in the selected component.** Under the hypotheses of the
previous statement and `selector ∈ A'`, `{base} ∪ A'` is contained in the component of
`selector` in `K \ A`.
Library: `ScalarPitchfork.Global.retainedWithBase_subset_selectedComponent` (with
`parentComponent`, `unilateralRemainder`, `selectedComponent` unfolded). -/
theorem retainedWithBase_subset_selectedComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc)
        selector := by
  exact _root_.ScalarPitchfork.Global.retainedWithBase_subset_selectedComponent hSelector
    hRetainedConnected hRetainedInSolution hAvoidRemoved

/-- **The base point lies in the selected component.** Under the hypotheses of the
previous statement, `base` lies in the component of `selector` in `K \ A`.
Library: `ScalarPitchfork.Global.base_mem_selectedComponent` (with `parentComponent`,
`unilateralRemainder`, `selectedComponent` unfolded). -/
theorem base_mem_selectedComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    base ∈ connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc)
      selector := by
  exact _root_.ScalarPitchfork.Global.base_mem_selectedComponent hSelector
    hRetainedConnected hRetainedInSolution hAvoidRemoved

/-- **The selected component lies in the solution set.** The component of `selector` in
`K \ A` is contained in `S`, where `K` is the component of `base` in `S`.
Library: `ScalarPitchfork.Global.selectedComponent_subset_solutionClosure` (with
`parentComponent`, `unilateralRemainder`, `selectedComponent` unfolded). -/
theorem selectedComponent_subset_solutionClosure {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base selector : X} :
    connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc) selector ⊆
      solutionClosure := by
  exact _root_.ScalarPitchfork.Global.selectedComponent_subset_solutionClosure

end ScalarPitchforkAudit.ScalarPitchfork.Global
