/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Branch

/-!
# The stronger remainder bound

A stronger form of the remainder hypotheses of `ScalarPitchfork.Existence`: the value bound
`|R(tau, z)| ≤ C (z ^ 2 tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)` and the derivative bound
`|Rs(tau, z)| ≤ C (|z| tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)`. These hold, for instance, when the
linear part of the field along the axis `z = 0` is exactly `alpha * tau * z`
(see `ScalarPitchfork.strongBound_iff_axis`).

For `|z| ≤ 1` the stronger bounds imply the weak ones, so the zero-level conclusions, the
existence of the branches and the packaged branch-curve statement transfer unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

open Filter Topology

/-! ## The stronger bound implies the weak bound -/

/-- The stronger value bound implies the weak value bound when `|z| ≤ 1`. -/
theorem value_bound_weak_of_strongBound (tau z R C : ℝ)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hR : |R| ≤ C * (z ^ 2 * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4)) :
    |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4) := by
  have hss : z ^ 2 ≤ |z| := by nlinarith [sq_abs z, abs_nonneg z]
  have h1 : z ^ 2 * tau ^ 2 ≤ |z| * tau ^ 2 :=
    mul_le_mul_of_nonneg_right hss (sq_nonneg tau)
  calc
    |R| ≤ C * (z ^ 2 * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4) := hR
    _ ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4) := by gcongr

/-- The stronger derivative bound `C (|z| tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)`
implies the weak derivative bound when `|z| ≤ 1`. -/
theorem deriv_bound_weak_of_strongBound (tau z Rs C : ℝ)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hRs : |Rs| ≤ C * (|z| * tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3)) :
    |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := by
  have h1 : |z| * tau ^ 2 ≤ tau ^ 2 := by
    nlinarith [sq_nonneg tau]
  calc
    |Rs| ≤ C * (|z| * tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := hRs
    _ ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := by gcongr

/-! ## Conclusions under the stronger bound -/

/-- The conclusions of `equilibrium_core` from the stronger bounds. -/
theorem equilibrium_core_of_strongBound (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (z ^ 2 * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (|z| * tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : absorbedConst alpha beta C * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| :=
  equilibrium_core alpha beta tau z R Rs ds C halpha hbeta hs hC hs1 heta1 hetaC
    hroot hderiv (value_bound_weak_of_strongBound tau z R C hC hs1 hR)
    (deriv_bound_weak_of_strongBound tau z Rs C hC hs1 hRs) hrectangle

/-- The conclusions of `exists_branch_eventually` from the stronger bounds. -/
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
        pitchforkField alpha beta R tau z = 0 ∧
        abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (pitchforkField alpha beta R tau) z * beta < 0 :=
  exists_branch_eventually alpha beta C r R Rs halpha hbeta hC hr hr1
    (fun e z he hs => value_bound_weak_of_strongBound e z (R e z) C hC (hs.trans hr1)
      (hRval e z he hs))
    hRder
    (fun e z he hs => deriv_bound_weak_of_strongBound e z (Rs e z) C hC (hs.trans hr1)
      (hRs e z he hs))

/-- Continuity, the limit at `0` and local uniqueness of the branches from the
stronger bounds (`z ^ 2 tau ^ 2` in the value bound, `|z| tau ^ 2` in the derivative bound),
through the weak bounds. -/
theorem branch_curves_of_strongBound (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
        {tau | BranchNhd alpha beta C r tau} ∧
      Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) ∧
      ∀ tau, BranchNhd alpha beta C r tau → 0 < tau * beta →
        ∃! z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z := by
  have hRval' : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := fun e z he hs =>
    value_bound_weak_of_strongBound e z (R e z) C hC (hs.trans hr1) (hRval e z he hs)
  have hRs' : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) := fun e z he hs =>
    deriv_bound_weak_of_strongBound e z (Rs e z) C hC (hs.trans hr1) (hRs e z he hs)
  exact ⟨branch_continuousOn alpha beta C r R Rs halpha hbeta hC hr hr1 hRval' hRder hRs' hRcont
      sgn hsgn,
    branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval' hRder hRs' sgn hsgn,
    fun tau h hside => branchRoot_existsUnique alpha beta C r tau R Rs halpha hbeta hC hr hr1
      hRval' hRder hRs' h hside sgn hsgn⟩

end ScalarPitchfork
