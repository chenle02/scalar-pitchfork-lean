/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# The exact cubic pitchfork normal form

For real coefficients `alpha`, `beta` and a parameter `tau`, the scalar field

`cubicField alpha beta tau A = alpha * tau * A - beta * A ^ 3`

is the normal form of a pitchfork bifurcation in the amplitude `A` at `(tau, A) = (0, 0)`: `alpha` is the
transversality coefficient and `beta` the cubic coefficient.

This file proves the exact algebra of its nonzero zeros:
* a nonzero zero satisfies `A ^ 2 = alpha * tau / beta` and, for `alpha > 0`, exists only on
  the side `tau * beta > 0`;
* on that side the nonzero zeros are exactly `± √(alpha * tau / beta)`;
* the derivative in `A` at a nonzero zero is `-2 * alpha * tau`, so it is negative for a
  supercritical (`beta > 0`) and positive for a subcritical (`beta < 0`) branch.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

/-- The cubic pitchfork normal form `alpha * tau * A - beta * A ^ 3`. -/
noncomputable def cubicField (alpha beta tau A : ℝ) : ℝ :=
  alpha * tau * A - beta * A ^ 3

/-! ## Nonzero zeros -/

/-- Every nonzero zero of the cubic field satisfies `A ^ 2 = alpha * tau / beta`. -/
theorem nonzero_equilibrium_sq (alpha beta tau A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    A ^ 2 = alpha * tau / beta := by
  unfold cubicField at hroot
  field_simp
  apply (mul_left_cancel₀ hA)
  nlinarith

/-- With `alpha > 0`, a nonzero zero exists only on the side where
`tau * beta > 0`. -/
theorem nonzero_equilibrium_branch_side (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    0 < tau * beta := by
  have hratio : 0 < alpha * tau / beta := by
    rw [← nonzero_equilibrium_sq alpha beta tau A hbeta hA hroot]
    exact sq_pos_of_ne_zero hA
  rcases (div_pos_iff.mp hratio) with h | h
  · have hchi : 0 < tau :=
      pos_of_mul_pos_left (by simpa [mul_comm] using h.1) halpha.le
    exact mul_pos hchi h.2
  · have hchi : tau < 0 :=
      neg_of_mul_neg_left (by simpa [mul_comm] using h.1) halpha.le
    exact mul_pos_of_neg_of_neg hchi h.2

/-- The squared amplitude `alpha * tau / beta` is positive on the side `tau * beta > 0`. -/
theorem amplitude_sq_pos (alpha beta tau : ℝ)
    (halpha : 0 < alpha) (hside : 0 < tau * beta) :
    0 < alpha * tau / beta := by
  have hchi_beta : 0 < tau / beta := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  rw [show alpha * tau / beta = alpha * (tau / beta) by ring]
  exact mul_pos halpha hchi_beta

/-- `± √(alpha * tau / beta)` are zeros of the cubic field on the side `tau * beta > 0`. -/
theorem branch_amplitudes (alpha beta tau : ℝ)
    (halpha : 0 < alpha) (hside : 0 < tau * beta) :
    cubicField alpha beta tau (Real.sqrt (alpha * tau / beta)) = 0 ∧
      cubicField alpha beta tau (-Real.sqrt (alpha * tau / beta)) = 0 := by
  have hsquare : (Real.sqrt (alpha * tau / beta)) ^ 2 = alpha * tau / beta :=
    Real.sq_sqrt (amplitude_sq_pos alpha beta tau halpha hside).le
  have hbeta : beta ≠ 0 := by
    intro h
    simp [h] at hside
  have hcoef : alpha * tau - beta * Real.sqrt (alpha * tau / beta) ^ 2 = 0 := by
    rw [hsquare]
    field_simp
    ring
  constructor
  · unfold cubicField
    calc
      alpha * tau * Real.sqrt (alpha * tau / beta) -
          beta * Real.sqrt (alpha * tau / beta) ^ 3 =
          Real.sqrt (alpha * tau / beta) *
            (alpha * tau - beta * Real.sqrt (alpha * tau / beta) ^ 2) := by ring
      _ = 0 := by rw [hcoef, mul_zero]
  · unfold cubicField
    calc
      alpha * tau * (-Real.sqrt (alpha * tau / beta)) -
          beta * (-Real.sqrt (alpha * tau / beta)) ^ 3 =
          -Real.sqrt (alpha * tau / beta) *
            (alpha * tau - beta * Real.sqrt (alpha * tau / beta) ^ 2) := by ring
      _ = 0 := by rw [hcoef, mul_zero]

/-- The only nonzero zeros of the cubic field are
`± √(alpha * tau / beta)`. -/
theorem nonzero_equilibrium_eq_branch (alpha beta tau A : ℝ)
    (_halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    A = Real.sqrt (alpha * tau / beta) ∨
      A = -Real.sqrt (alpha * tau / beta) := by
  have hsq := nonzero_equilibrium_sq alpha beta tau A hbeta hA hroot
  have hratio : 0 ≤ alpha * tau / beta := by
    rw [← hsq]
    positivity
  have hsqrt : (Real.sqrt (alpha * tau / beta)) ^ 2 = alpha * tau / beta :=
    Real.sq_sqrt hratio
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hsqrt.symm)

/-! ## The derivative at a nonzero zero -/

/-- The derivative of the cubic field in `A`. -/
theorem deriv_cubicField (alpha beta tau A : ℝ) :
    deriv (cubicField alpha beta tau) A =
      alpha * tau - 3 * beta * A ^ 2 := by
  have hlin : HasDerivAt (fun x : ℝ => alpha * tau * x) (alpha * tau) A := by
    simpa using (hasDerivAt_id A).const_mul (alpha * tau)
  have hcub : HasDerivAt (fun x : ℝ => beta * x ^ 3) (3 * beta * A ^ 2) A := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id A).pow 3).const_mul beta
  change deriv (fun x : ℝ => alpha * tau * x - beta * x ^ 3) A =
    alpha * tau - 3 * beta * A ^ 2
  exact (hlin.sub hcub).deriv

/-- At a nonzero zero, the derivative of the cubic field in `A` is
`-2 * alpha * tau`. -/
theorem deriv_cubicField_at_branch (alpha beta tau A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    deriv (cubicField alpha beta tau) A = -2 * alpha * tau := by
  rw [deriv_cubicField]
  rw [nonzero_equilibrium_sq alpha beta tau A hbeta hA hroot]
  field_simp [hbeta]
  ring

/-- On a supercritical branch (`beta > 0`) the derivative at a nonzero zero is negative. -/
theorem supercritical_deriv_neg (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    deriv (cubicField alpha beta tau) A < 0 := by
  rw [deriv_cubicField_at_branch alpha beta tau A hbeta.ne' hA hroot]
  have hside := nonzero_equilibrium_branch_side alpha beta tau A
    halpha hbeta.ne' hA hroot
  have hchi : 0 < tau := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact h.1
    · exact (hbeta.asymm h.2).elim
  nlinarith [mul_pos halpha hchi]

/-- On a subcritical branch (`beta < 0`) the derivative at a nonzero zero is positive. -/
theorem subcritical_deriv_pos (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta < 0) (hA : A ≠ 0)
    (hroot : cubicField alpha beta tau A = 0) :
    0 < deriv (cubicField alpha beta tau) A := by
  rw [deriv_cubicField_at_branch alpha beta tau A hbeta.ne hA hroot]
  have hside := nonzero_equilibrium_branch_side alpha beta tau A
    halpha hbeta.ne hA hroot
  have hchi : tau < 0 := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact (hbeta.asymm h.2).elim
    · exact h.1
  nlinarith [mul_pos halpha (neg_pos.mpr hchi)]

end ScalarPitchfork
