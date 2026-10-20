/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Cubic

/-!
# Zeros of a perturbed cubic: side, derivative sign and amplitude

Finite inequalities at a given nonzero zero `z` of a perturbed cubic equation
`alpha * tau * z - beta * z ^ 3 + R = 0`, or of the divided equation
`alpha * tau - beta * z ^ 2 + e = 0` (with `e = R / z`).

Under a quantitative bound on the remainder, and a separate bound on the derivative
remainder, this file proves:
* the zero lies on the side `tau * beta > 0` (`remainder_equilibrium_side`);
* the derivative of the field at the zero has sign opposite to `beta`
  (`remainder_equilibrium_derivative_sign`);
* `|z|` is `√(alpha * tau / beta)` up to an error `O(z ^ 2)` when the divided remainder is
  `O(|z| ^ 3)` (`abs_sub_sqrt_le_of_cubic_remainder`), and up to an explicit error `O(|tau|)`
  under the mixed bound `|e| ≤ C (|tau| + |z|) z ^ 2` (`magnitude_error_of_mixed_bound`);
* all three conclusions together from bounds on `R` and on the derivative remainder
  (`perturbed_equilibrium_core`).

The existence of the zero is a hypothesis here; existence is proved in
`ScalarPitchfork.Existence`.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

/-! ## Side and derivative sign -/

/-- A nonzero zero of the divided equation `alpha * tau - beta * z ^ 2 + e = 0`
lies on the side `tau * beta > 0` whenever `|e| < |beta| * z ^ 2`. The premise is a
quantitative remainder bound, not an existence assertion. -/
theorem remainder_equilibrium_side (alpha beta tau z e : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (hsmall : |e| < |beta| * z ^ 2) : 0 < tau * beta := by
  have he := abs_le.mp (le_refl |e|)
  rcases lt_or_gt_of_ne hbeta with hb | hb
  · rw [abs_of_neg hb] at hsmall
    have hae : alpha * tau < 0 := by nlinarith
    have heta : tau < 0 := by
      by_contra h
      have hp := mul_nonneg halpha.le (le_of_not_gt h)
      linarith
    exact mul_pos_of_neg_of_neg heta hb
  · rw [abs_of_pos hb] at hsmall
    have hae : 0 < alpha * tau := by nlinarith
    have heta : 0 < tau := (mul_pos_iff_of_pos_left halpha).mp hae
    exact mul_pos heta hb

/-- Separate bounds on the divided remainder `e` and on the derivative
remainder `es` give the sign of the derivative `ds = alpha * tau - 3 * beta * z ^ 2 + es`:
`ds * beta < 0`. No derivative estimate is inferred from a size bound. -/
theorem remainder_equilibrium_derivative_sign (alpha beta tau z e es ds : ℝ)
    (hbeta : beta ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + es)
    (hsmall : |e| + |es| < 2 * |beta| * z ^ 2) : ds * beta < 0 := by
  have he := abs_le.mp (le_refl |e|)
  have hes := abs_le.mp (le_refl |es|)
  rcases lt_or_gt_of_ne hbeta with hb | hb
  · rw [abs_of_neg hb] at hsmall
    have hds : 0 < ds := by nlinarith
    exact mul_neg_of_pos_of_neg hds hb
  · rw [abs_of_pos hb] at hsmall
    have hds : ds < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos hds hb

/-! ## The square-root amplitude -/

/-- Exact squared-amplitude error at a zero of the divided equation. -/
theorem remainder_squared_amplitude_error (alpha beta tau z e : ℝ)
    (hbeta : beta ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0) :
    |z ^ 2 - alpha * tau / beta| = |e| / |beta| := by
  have hid : z ^ 2 - alpha * tau / beta = e / beta := by
    apply (eq_div_iff hbeta).mpr
    field_simp
    nlinarith
  rw [hid, abs_div]

/-- Factoring a difference of squares bounds the error of a square root. -/
theorem magnitude_sqrt_error (z t : ℝ) (hs : z ≠ 0) (ht : 0 ≤ t) :
    abs (|z| - Real.sqrt t) ≤ |z ^ 2 - t| / |z| := by
  have hspos : 0 < |z| := abs_pos.mpr hs
  have hf : z ^ 2 - t = (|z| - Real.sqrt t) * (|z| + Real.sqrt t) := by
    nlinarith [sq_abs z, Real.sq_sqrt ht]
  apply (le_div_iff₀ hspos).mpr
  rw [hf, abs_mul, abs_of_nonneg (add_nonneg (abs_nonneg z) (Real.sqrt_nonneg t))]
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.sqrt_nonneg t)) (abs_nonneg _)

/-- A cubic bound `|e| ≤ C |z| ^ 3` on the divided remainder gives a
quadratic error for the square-root amplitude:
`| |z| - √(alpha * tau / beta) | ≤ C z ^ 2 / |beta|`. -/
theorem abs_sub_sqrt_le_of_cubic_remainder (alpha beta tau z e C : ℝ)
    (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (ht : 0 ≤ alpha * tau / beta) (herr : |e| ≤ C * |z| ^ 3) :
    abs (|z| - Real.sqrt (alpha * tau / beta)) ≤ C * z ^ 2 / |beta| := by
  have hb : |beta| ≠ 0 := abs_ne_zero.mpr hbeta
  have hsn : |z| ≠ 0 := abs_ne_zero.mpr hs
  calc
    abs (|z| - Real.sqrt (alpha * tau / beta))
        ≤ |z ^ 2 - alpha * tau / beta| / |z| := magnitude_sqrt_error z _ hs ht
    _ = (|e| / |beta|) / |z| := by
      rw [remainder_squared_amplitude_error alpha beta tau z e hbeta hroot]
    _ ≤ (C * |z| ^ 3 / |beta|) / |z| :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right herr (abs_nonneg beta)) (abs_nonneg z)
    _ = C * z ^ 2 / |beta| := by
      rw [show |z| ^ 3 = |z| ^ 2 * |z| by ring, sq_abs]
      field_simp

/-! ## The mixed remainder bound -/

/-- A small divided remainder makes `alpha * |tau|` comparable to
`|beta| * z ^ 2`. -/
theorem parameter_amplitude_bounds (alpha beta tau z e : ℝ)
    (halpha : 0 < alpha)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (hsmall : |e| ≤ |beta| / 2 * z ^ 2) :
    |beta| / 2 * z ^ 2 ≤ alpha * |tau| ∧
      alpha * |tau| ≤ 3 * |beta| / 2 * z ^ 2 := by
  have hid1 : beta * z ^ 2 = alpha * tau + e := by linarith
  have h1 := abs_add_le (alpha * tau) e
  rw [← hid1] at h1
  simp only [abs_mul, abs_of_pos halpha, abs_of_nonneg (sq_nonneg z)] at h1
  have hid2 : alpha * tau = beta * z ^ 2 + -e := by linarith
  have h2 := abs_add_le (beta * z ^ 2) (-e)
  rw [← hid2] at h2
  simp only [abs_mul, abs_neg, abs_of_pos halpha, abs_of_nonneg (sq_nonneg z)] at h2
  constructor <;> nlinarith

/-- If `|tau| ≤ D z ^ 2` and `|z| ≤ 1`, the mixed bound
`|e| ≤ C (|tau| + |z|) z ^ 2` implies a cubic bound `|e| ≤ C (D + 1) |z| ^ 3`. -/
theorem divided_remainder_cubic_bound (C D tau z e : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hs : |z| ≤ 1)
    (heta : |tau| ≤ D * z ^ 2)
    (herr : |e| ≤ C * (|tau| + |z|) * z ^ 2) :
    |e| ≤ (C * (D + 1)) * |z| ^ 3 := by
  have hs2 : z ^ 2 ≤ |z| := by nlinarith [sq_abs z, abs_nonneg z]
  have he1 : |tau| ≤ D * |z| :=
    heta.trans (mul_le_mul_of_nonneg_left hs2 hD)
  have hsum : |tau| + |z| ≤ (D + 1) * |z| := by nlinarith
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum hC) (sq_nonneg z)
  calc
    |e| ≤ C * (|tau| + |z|) * z ^ 2 := herr
    _ ≤ C * ((D + 1) * |z|) * z ^ 2 := hm
    _ = (C * (D + 1)) * |z| ^ 3 := by rw [← sq_abs z]; ring

/-- The mixed bound `|e| ≤ C (|tau| + |z|) z ^ 2` on the divided remainder
yields an explicit `O(|tau|)` error for the square-root amplitude, after absorption on a
small rectangle. -/
theorem magnitude_error_of_mixed_bound (alpha beta tau z e C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (herr : |e| ≤ C * (|tau| + |z|) * z ^ 2)
    (hrectangle : C * (|tau| + |z|) ≤ |beta| / 2) :
    abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
      (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hs2 : 0 < z ^ 2 := sq_pos_of_ne_zero hs
  have hsmall : |e| ≤ |beta| / 2 * z ^ 2 :=
    herr.trans (mul_le_mul_of_nonneg_right hrectangle hs2.le)
  have hstrict : |e| < |beta| * z ^ 2 := by nlinarith [mul_pos hb hs2]
  have hside := remainder_equilibrium_side alpha beta tau z e halpha hbeta hroot hstrict
  have ht := amplitude_sq_pos alpha beta tau halpha hside
  obtain ⟨hlow, hupp⟩ := parameter_amplitude_bounds alpha beta tau z e halpha hroot hsmall
  let D : ℝ := 3 * |beta| / (2 * alpha)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have heta : |tau| ≤ D * z ^ 2 := by
    have hdiv : |tau| ≤ (3 * |beta| / 2 * z ^ 2) / alpha :=
      (le_div_iff₀ halpha).mpr (by nlinarith)
    calc
      |tau| ≤ (3 * |beta| / 2 * z ^ 2) / alpha := hdiv
      _ = D * z ^ 2 := by dsimp [D]; ring
  have hsq : z ^ 2 ≤ (2 * alpha / |beta|) * |tau| := by
    have hdiv : z ^ 2 ≤ (2 * alpha * |tau|) / |beta| :=
      (le_div_iff₀ hb).mpr (by nlinarith)
    calc
      z ^ 2 ≤ (2 * alpha * |tau|) / |beta| := hdiv
      _ = (2 * alpha / |beta|) * |tau| := by ring
  have hec := divided_remainder_cubic_bound C D tau z e hC hD hs1 heta herr
  have hamp := abs_sub_sqrt_le_of_cubic_remainder alpha beta tau z e (C * (D + 1))
    hbeta hs hroot ht.le hec
  have hcoef : 0 ≤ C * (D + 1) / |beta| := by positivity
  calc
    abs (|z| - Real.sqrt (alpha * tau / beta)) ≤ C * (D + 1) * z ^ 2 / |beta| := hamp
    _ = (C * (D + 1) / |beta|) * z ^ 2 := by ring
    _ ≤ (C * (D + 1) / |beta|) * ((2 * alpha / |beta|) * |tau|) :=
      mul_le_mul_of_nonneg_left hsq hcoef
    _ = (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
      dsimp [D]
      ring

/-- Zero-level conclusions for the perturbed cubic
`alpha * tau * z - beta * z ^ 3 + R = 0` from the bounds
`|R| ≤ C (|tau| |z| ^ 3 + z ^ 4)` and `|Rs| ≤ C (|tau| z ^ 2 + |z| ^ 3)`: the side condition
`tau * beta > 0`, the derivative sign `ds * beta < 0`, and the square-root amplitude with an
`O(|tau|)` error. The existence of the zero is a hypothesis. -/
theorem perturbed_equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|tau| * |z| ^ 3 + |z| ^ 4))
    (hRs : |Rs| ≤ C * (|tau| * z ^ 2 + |z| ^ 3))
    (hrectangle : C * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
        (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  have hdivroot : alpha * tau - beta * z ^ 2 + R / z = 0 := by
    calc
      alpha * tau - beta * z ^ 2 + R / z =
          (alpha * tau * z - beta * z ^ 3 + R) / z := by
        field_simp [hs]
      _ = 0 := by rw [hroot]; simp
  have hdivR : |R / z| ≤ C * (|tau| + |z|) * z ^ 2 := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hs)).mpr
    calc
      |R| ≤ C * (|tau| * |z| ^ 3 + |z| ^ 4) := hR
      _ = C * (|tau| + |z|) * z ^ 2 * |z| := by rw [← sq_abs z]; ring
  have hRs' : |Rs| ≤ C * (|tau| + |z|) * z ^ 2 := by
    calc
      |Rs| ≤ C * (|tau| * z ^ 2 + |z| ^ 3) := hRs
      _ = C * (|tau| + |z|) * z ^ 2 := by rw [← sq_abs z]; ring
  have hs2 : 0 < z ^ 2 := sq_pos_of_ne_zero hs
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hrect := mul_le_mul_of_nonneg_right hrectangle hs2.le
  have hsmallR : |R / z| < |beta| * z ^ 2 := by
    nlinarith [mul_pos hb hs2]
  have hsmallBoth : |R / z| + |Rs| < 2 * |beta| * z ^ 2 := by
    nlinarith [mul_pos hb hs2]
  exact ⟨remainder_equilibrium_side alpha beta tau z (R / z)
      halpha hbeta hdivroot hsmallR,
    remainder_equilibrium_derivative_sign alpha beta tau z (R / z) Rs ds
      hbeta hdivroot hderiv hsmallBoth,
    magnitude_error_of_mixed_bound alpha beta tau z (R / z) C
      halpha hbeta hs hC hs1 hdivroot hdivR hrectangle⟩

end ScalarPitchfork
