/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Perturbed

/-!
# Existence of the pitchfork branches under a weak remainder bound

The perturbed pitchfork field is

`pitchforkField alpha beta R tau z = alpha * tau * z - beta * z ^ 3 + R tau z`.

On a box `|tau|, |z| ≤ r ≤ 1` the remainder is assumed to satisfy the value bound
`|R(tau, z)| ≤ C (|z| tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)`, to have a derivative
`HasDerivAt (R tau) (Rs tau z) z`, and to satisfy the matching derivative bound
`|Rs(tau, z)| ≤ C (tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)`.

Along a small zero the parameter is controlled by the squared amplitude,
`|tau| ≤ ampConst alpha beta C * z ^ 2`. This absorbs the term `|z| tau ^ 2` into the
mixed form handled by `perturbed_equilibrium_core`, with the constant `absorbedConst`
(`equilibrium_core`).

The intermediate value theorem then gives, for every small `tau` on the side
`tau * beta > 0`, nontrivial zeros of both signs with amplitude
`√(alpha * tau / beta) + O(|tau|)` and derivative of sign opposite to `beta`
(`exists_branch_eventually`). Conversely, every small nontrivial zero lies on the side
`tau * beta > 0` and has that derivative sign (`branch_side_eventually`). Uniqueness and
continuity of the branches are proved in `ScalarPitchfork.Branch`.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

open Filter Topology

/-- The constant `D` in `|tau| ≤ D z ^ 2` along a small zero. -/
noncomputable def ampConst (alpha beta C : ℝ) : ℝ :=
  2 * (|beta| + 2 * C) / alpha

/-- The constant of the remainder bound after absorbing `|z| tau ^ 2`. -/
noncomputable def absorbedConst (alpha beta C : ℝ) : ℝ :=
  C * (ampConst alpha beta C + 1)

theorem ampConst_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ ampConst alpha beta C := by
  unfold ampConst
  positivity

theorem absorbedConst_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ absorbedConst alpha beta C := by
  unfold absorbedConst
  have := ampConst_nonneg alpha beta C halpha hC
  positivity

/-! ## Absorbing `|z| tau ^ 2` along a zero -/

/-- Along a small nonzero zero of the divided equation with the weak divided
remainder bound, the parameter is controlled by the squared amplitude:
`|tau| ≤ ampConst alpha beta C * z ^ 2`. -/
theorem parameter_le_amp_sq (alpha beta tau z e C : ℝ)
    (halpha : 0 < alpha) (hC : 0 ≤ C)
    (heta1 : |tau| ≤ 1) (hs1 : |z| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (he : |e| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3)) :
    |tau| ≤ ampConst alpha beta C * z ^ 2 := by
  have hid : alpha * tau = beta * z ^ 2 + -e := by linarith
  have h1 := abs_add_le (beta * z ^ 2) (-e)
  rw [← hid] at h1
  simp only [abs_mul, abs_neg, abs_of_pos halpha, abs_of_nonneg (sq_nonneg z)] at h1
  have hs3 : |z| ^ 3 ≤ z ^ 2 := by
    rw [← sq_abs z]
    nlinarith [abs_nonneg z, sq_nonneg |z|]
  have heta2 : tau ^ 2 = |tau| * |tau| := by rw [← sq_abs tau]; ring
  have hCeta : C * tau ^ 2 ≤ alpha / 2 * |tau| := by
    rw [heta2]; nlinarith [abs_nonneg tau]
  have hsC : C * (z ^ 2 * |tau|) ≤ C * z ^ 2 := by
    have := mul_le_mul_of_nonneg_left heta1 (sq_nonneg z)
    nlinarith
  have hs3C : C * |z| ^ 3 ≤ C * z ^ 2 := mul_le_mul_of_nonneg_left hs3 hC
  have hmain : alpha / 2 * |tau| ≤ (|beta| + 2 * C) * z ^ 2 := by nlinarith
  unfold ampConst
  rw [div_mul_eq_mul_div, le_div_iff₀ halpha]
  nlinarith

/-- Pure absorption step: once `|tau| ≤ D z ^ 2`, the weak divided remainder form
is bounded by `(D + 1) (|tau| + |z|) z ^ 2`. -/
theorem divided_absorb (tau z D : ℝ)
    (heta : |tau| ≤ D * z ^ 2) :
    tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3 ≤ (D + 1) * (|tau| + |z|) * z ^ 2 := by
  have heta2 : tau ^ 2 ≤ D * z ^ 2 * |tau| := by
    rw [← sq_abs tau, sq]
    exact mul_le_mul_of_nonneg_right heta (abs_nonneg tau)
  have hs3 : |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
  rw [hs3]
  have hDs : 0 ≤ D * z ^ 2 := (abs_nonneg tau).trans heta
  nlinarith [abs_nonneg tau, abs_nonneg z, sq_nonneg z, mul_nonneg hDs (abs_nonneg z)]

/-- Along a zero (`|tau| ≤ D z ^ 2`) the weak value bound implies the value
bound assumed by `perturbed_equilibrium_core`. -/
theorem value_bound_absorbed (tau z R C D : ℝ) (hC : 0 ≤ C)
    (heta : |tau| ≤ D * z ^ 2)
    (hR : |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4)) :
    |R| ≤ (C * (D + 1)) * (|tau| * |z| ^ 3 + |z| ^ 4) := by
  have hab := divided_absorb tau z D heta
  have hfac : |z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4 =
      |z| * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := by
    rw [← (by decide : Even 4).pow_abs z, ← sq_abs z]; ring
  calc
    |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4) := hR
    _ = C * |z| * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := by rw [hfac]; ring
    _ ≤ C * |z| * ((D + 1) * (|tau| + |z|) * z ^ 2) := by
      have : 0 ≤ C * |z| := mul_nonneg hC (abs_nonneg z)
      exact mul_le_mul_of_nonneg_left hab this
    _ = (C * (D + 1)) * (|tau| * |z| ^ 3 + |z| ^ 4) := by rw [← sq_abs z]; ring

/-- Along a zero (`|tau| ≤ D z ^ 2`) the weak derivative bound implies the
derivative bound assumed by `perturbed_equilibrium_core`. -/
theorem deriv_bound_absorbed (tau z Rs C D : ℝ) (hC : 0 ≤ C)
    (heta : |tau| ≤ D * z ^ 2)
    (hRs : |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3)) :
    |Rs| ≤ (C * (D + 1)) * (|tau| * z ^ 2 + |z| ^ 3) := by
  have hab := divided_absorb tau z D heta
  calc
    |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := hRs
    _ ≤ C * ((D + 1) * (|tau| + |z|) * z ^ 2) := mul_le_mul_of_nonneg_left hab hC
    _ = (C * (D + 1)) * (|tau| * z ^ 2 + |z| ^ 3) := by rw [← sq_abs z]; ring

/-! ## Zero-level conclusions under the weak bound -/

/-- Zero-level conclusions under the weak remainder bounds. For a nonzero small zero
`z` of `alpha * tau * z - beta * z ^ 3 + R = 0` with
`|R| ≤ C (|z| tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)`, and the derivative
`ds = alpha * tau - 3 * beta * z ^ 2 + Rs` with `|Rs| ≤ C (tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)`:
the side condition `tau * beta > 0`, the derivative sign `ds * beta < 0`, and the
square-root amplitude `|z| = √(alpha * tau / beta) + O(|tau|)`. -/
theorem equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : absorbedConst alpha beta C * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| := by
  have hsabs : 0 < |z| := abs_pos.mpr hs
  have hdivroot : alpha * tau - beta * z ^ 2 + R / z = 0 := by
    calc
      alpha * tau - beta * z ^ 2 + R / z =
          (alpha * tau * z - beta * z ^ 3 + R) / z := by
        field_simp [hs]
      _ = 0 := by rw [hroot]; simp
  have hdivR : |R / z| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) := by
    rw [abs_div]
    apply (div_le_iff₀ hsabs).mpr
    calc
      |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4) := hR
      _ = C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3) * |z| := by
        rw [← (by decide : Even 4).pow_abs z, ← sq_abs z]; ring
  have heta := parameter_le_amp_sq alpha beta tau z (R / z) C
    halpha hC heta1 hs1 hetaC hdivroot hdivR
  exact perturbed_equilibrium_core alpha beta tau z R Rs ds (absorbedConst alpha beta C)
    halpha hbeta hs (absorbedConst_nonneg alpha beta C halpha hC) hs1 hroot hderiv
    (value_bound_absorbed tau z R C _ hC heta hR)
    (deriv_bound_absorbed tau z Rs C _ hC heta hRs) hrectangle

/-! ## Existence of the two nontrivial zeros (intermediate value theorem) -/

/-- On the side `tau * beta > 0`, the squared amplitude `alpha * tau / beta` equals
`alpha * |tau| / |beta|`. -/
theorem amp_sq_eq_abs (alpha beta tau : ℝ) (hside : 0 < tau * beta) :
    alpha * tau / beta = alpha * |tau| / |beta| := by
  have hb : beta ≠ 0 := by rintro rfl; simp at hside
  rcases mul_pos_iff.mp hside with h | h
  · rw [abs_of_pos h.1, abs_of_pos h.2]
  · rw [abs_of_neg h.1, abs_of_neg h.2]
    field_simp

/-- Size of the weak value remainder below the amplitude scale
`z ^ 2 ≤ 2 * alpha * tau / beta`. -/
theorem weak_value_lt_on_window (alpha beta tau z R C : ℝ)
    (hside : 0 < tau * beta) (hC : 0 ≤ C) (hs : 0 < z)
    (hs2 : z ^ 2 ≤ 2 * (alpha * tau / beta))
    (hR : |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hsmall : C * (|tau| + 2 * (alpha * tau / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2) :
    |R| < z * (alpha / 2 * |tau|) := by
  have heta : 0 < |tau| := abs_pos.mpr (by rintro rfl; simp at hside)
  have hbeta : 0 < |beta| := abs_pos.mpr (by rintro rfl; simp at hside)
  set t := alpha * tau / beta with ht
  have htabs : t = alpha * |tau| / |beta| := amp_sq_eq_abs alpha beta tau hside
  have hsle : z ≤ Real.sqrt (2 * t) := by
    calc z = Real.sqrt (z ^ 2) := (Real.sqrt_sq hs.le).symm
      _ ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt hs2
  have hcube : z ^ 3 ≤ |tau| * (2 * alpha * Real.sqrt (2 * t) / |beta|) := by
    have h2t : 2 * t = |tau| * (2 * alpha / |beta|) := by rw [htabs]; ring
    have hpos : 0 ≤ z ^ 2 := sq_nonneg z
    calc z ^ 3 = z * z ^ 2 := by ring
      _ ≤ Real.sqrt (2 * t) * (2 * t) :=
        mul_le_mul hsle hs2 hpos (Real.sqrt_nonneg _)
      _ = |tau| * (2 * alpha * Real.sqrt (2 * t) / |beta|) := by rw [h2t]; ring
  have hmid : z ^ 2 * |tau| ≤ |tau| * (2 * t) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs2 heta.le
  have hin : tau ^ 2 + z ^ 2 * |tau| + z ^ 3 ≤
      |tau| * (|tau| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|) := by
    have : tau ^ 2 = |tau| * |tau| := by rw [← sq_abs tau]; ring
    nlinarith
  have habs : |z| = z := abs_of_pos hs
  have hfac : |z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4 =
      z * (tau ^ 2 + z ^ 2 * |tau| + z ^ 3) := by rw [habs]; ring
  rw [hfac] at hR
  have hlt : C * (|tau| * (|tau| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|)) <
      alpha / 2 * |tau| := by
    have := mul_lt_mul_of_pos_left hsmall heta
    nlinarith
  calc
    |R| ≤ C * (z * (tau ^ 2 + z ^ 2 * |tau| + z ^ 3)) := hR
    _ = z * (C * (tau ^ 2 + z ^ 2 * |tau| + z ^ 3)) := by ring
    _ ≤ z * (C * (|tau| * (|tau| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin hC) hs.le
    _ < z * (alpha / 2 * |tau|) := mul_lt_mul_of_pos_left hlt hs

/-- Existence of a positive nontrivial zero on the side `tau * beta > 0`, with
`z ^ 2 ∈ [alpha tau / (2 beta), 2 alpha tau / beta]`. Only continuity of the remainder in
`z` and the weak value bound on the amplitude window are used. -/
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
  have hbeta : beta ≠ 0 := by rintro rfl; simp at hside
  have heta0 : tau ≠ 0 := by rintro rfl; simp at hside
  have ht : 0 < alpha * tau / beta := amplitude_sq_pos alpha beta tau halpha hside
  set t := alpha * tau / beta with htdef
  have hbt : beta * t = alpha * tau := by rw [htdef]; field_simp
  set s1 := Real.sqrt (t / 2) with hs1def
  set s2 := Real.sqrt (2 * t) with hs2def
  have hs1pos : 0 < s1 := Real.sqrt_pos.mpr (by positivity)
  have hs2pos : 0 < s2 := Real.sqrt_pos.mpr (by positivity)
  have hs1sq : s1 ^ 2 = t / 2 := Real.sq_sqrt (by positivity)
  have hs2sq : s2 ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  have hs12 : s1 ≤ s2 := Real.sqrt_le_sqrt (by linarith)
  set f : ℝ → ℝ := fun z => alpha * tau * z - beta * z ^ 3 + R z with hfdef
  set k : ℝ → ℝ := fun z => -(tau * f z) with hkdef
  have hR1 := weak_value_lt_on_window alpha beta tau s1 (R s1) C hside hC hs1pos
    (by rw [hs1sq]; linarith) (hR s1 hs1pos (by rw [hs1sq]; linarith)) hsmall
  have hR2 := weak_value_lt_on_window alpha beta tau s2 (R s2) C hside hC hs2pos
    (le_of_eq hs2sq) (hR s2 hs2pos (le_of_eq hs2sq)) hsmall
  have he2 : 0 < tau ^ 2 := by positivity
  have hetaR (x : ℝ) : |tau * R x| = |tau| * |R x| := abs_mul _ _
  have hf1 : f s1 = s1 * (alpha * tau / 2) + R s1 := by
    simp only [hfdef]
    have : s1 ^ 3 = s1 * (t / 2) := by rw [← hs1sq]; ring
    rw [this]; linear_combination (-s1 / 2) * hbt
  have hf2 : f s2 = -(s2 * (alpha * tau)) + R s2 := by
    simp only [hfdef]
    have : s2 ^ 3 = s2 * (2 * t) := by rw [← hs2sq]; ring
    rw [this]; linear_combination (-2 * s2) * hbt
  have habs_eta : |tau| * |tau| = tau ^ 2 := by rw [← sq_abs tau]; ring
  have hk1 : k s1 < 0 := by
    simp only [hkdef]
    rw [hf1]
    have hlt : |tau| * |R s1| < |tau| * (s1 * (alpha / 2 * |tau|)) :=
      mul_lt_mul_of_pos_left hR1 (abs_pos.mpr heta0)
    have hneg := neg_abs_le (tau * R s1)
    nlinarith [mul_pos hs1pos (mul_pos halpha he2), hetaR s1]
  have hk2 : 0 < k s2 := by
    simp only [hkdef]
    rw [hf2]
    have hlt : |tau| * |R s2| < |tau| * (s2 * (alpha / 2 * |tau|)) :=
      mul_lt_mul_of_pos_left hR2 (abs_pos.mpr heta0)
    have hle := le_abs_self (tau * R s2)
    nlinarith [mul_pos hs2pos (mul_pos halpha he2), hetaR s2]
  have hkcont : ContinuousOn k (Set.Icc s1 s2) := by
    have hpoly : Continuous fun z : ℝ => alpha * tau * z - beta * z ^ 3 := by fun_prop
    have hfc : ContinuousOn f (Set.Icc s1 s2) := hpoly.continuousOn.add hcont
    exact (continuousOn_const.mul hfc).neg
  obtain ⟨z, hsI, hks⟩ := intermediate_value_Icc hs12 hkcont ⟨hk1.le, hk2.le⟩
  have hfs : f z = 0 := by
    have : tau * f z = 0 := by simpa [hkdef] using hks
    exact (mul_eq_zero.mp this).resolve_left heta0
  have hspos : 0 < z := hs1pos.trans_le hsI.1
  refine ⟨z, hspos, ?_, ?_, hfs⟩
  · rw [← hs1sq]; exact pow_le_pow_left₀ hs1pos.le hsI.1 2
  · rw [← hs2sq]; exact pow_le_pow_left₀ hspos.le hsI.2 2

/-! ## Branch conclusions as `tau → 0` -/

/-- The perturbed pitchfork field `alpha * tau * z - beta * z ^ 3 + R tau z`. -/
def pitchforkField (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (tau z : ℝ) : ℝ :=
  alpha * tau * z - beta * z ^ 3 + R tau z

/-- The derivative of the perturbed pitchfork field in `z`. -/
theorem pitchforkField_hasDerivAt (alpha beta : ℝ) (R Rs : ℝ → ℝ → ℝ) (tau z : ℝ)
    (hd : HasDerivAt (R tau) (Rs tau z) z) :
    HasDerivAt (pitchforkField alpha beta R tau)
      (alpha * tau - 3 * beta * z ^ 2 + Rs tau z) z := by
  have hlin : HasDerivAt (fun x : ℝ => alpha * tau * x) (alpha * tau) z := by
    simpa using (hasDerivAt_id z).const_mul (alpha * tau)
  have hcub : HasDerivAt (fun x : ℝ => beta * x ^ 3) (3 * beta * z ^ 2) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id z).pow 3).const_mul beta
  exact (hlin.sub hcub).add hd

/-- The smallness conditions on the parameter `tau` used for one parameter value. -/
def BranchSmall (alpha beta C r tau : ℝ) : Prop :=
  |tau| ≤ r ∧ 2 * C * |tau| ≤ alpha ∧ 2 * (alpha * tau / beta) ≤ r ^ 2 ∧
    C * (|tau| + 2 * (alpha * tau / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2 ∧
    absorbedConst alpha beta C * (|tau| + Real.sqrt (2 * (alpha * tau / beta))) ≤ |beta| / 2

/-- All smallness conditions hold for every `tau` near `0`; the hypotheses of the
branch theorem are therefore not vacuous. -/
theorem branchSmall_eventually (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hr : 0 < r) :
    ∀ᶠ tau in 𝓝 (0 : ℝ), BranchSmall alpha beta C r tau := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hc1 : Continuous fun tau : ℝ => |tau| := by fun_prop
  have hc2 : Continuous fun tau : ℝ => 2 * C * |tau| := by fun_prop
  have hc3 : Continuous fun tau : ℝ => 2 * (alpha * tau / beta) := by fun_prop
  have hsq : Continuous fun tau : ℝ => Real.sqrt (2 * (alpha * tau / beta)) :=
    Real.continuous_sqrt.comp hc3
  have hc4 : Continuous fun tau : ℝ => C * (|tau| + 2 * (alpha * tau / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) := by
    exact continuous_const.mul ((hc1.add hc3).add
      ((continuous_const.mul hsq).div_const _))
  have hc5 : Continuous fun tau : ℝ =>
      absorbedConst alpha beta C * (|tau| + Real.sqrt (2 * (alpha * tau / beta))) :=
    continuous_const.mul (hc1.add hsq)
  have e1 := (hc1.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := r))
    (by simpa using hr)
  have e2 := (hc2.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := alpha))
    (by simpa using halpha)
  have e3 := (hc3.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := r ^ 2))
    (by simpa using pow_pos hr 2)
  have e4 := (hc4.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := alpha / 2))
    (by simpa using half_pos halpha)
  have e5 := (hc5.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := |beta| / 2))
    (by simpa using half_pos hb)
  filter_upwards [e1, e2, e3, e4, e5] with tau h1 h2 h3 h4 h5
  exact ⟨h1.le, h2.le, h3.le, h4, h5.le⟩

/-- At one admissible `tau` on the side `tau * beta > 0`: a positive and a negative
nontrivial zero, each with the square-root amplitude up to `O(|tau|)` and with
`(∂_z field) * beta < 0`. -/
theorem exists_branch_at (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchSmall alpha beta C r tau) (hside : 0 < tau * beta) :
    ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
      pitchforkField alpha beta R tau z = 0 ∧
      abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
      deriv (pitchforkField alpha beta R tau) z * beta < 0 := by
  obtain ⟨hetar, hetaC, h2t, hwin, hrect⟩ := hsmall
  intro sgn hsgn
  have hsgn2 : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgnabs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  set t := alpha * tau / beta with htdef
  -- the remainder seen in the coordinate `x = sgn * z`
  set R' : ℝ → ℝ := fun x => sgn * R tau (sgn * x) with hR'def
  have hwin_le (x : ℝ) (hx : 0 < x) (hx2 : x ^ 2 ≤ 2 * t) : |sgn * x| ≤ r := by
    rw [abs_mul, hsgnabs, one_mul, abs_of_pos hx]
    nlinarith
  have hR'b : ∀ x, 0 < x → x ^ 2 ≤ 2 * t →
      |R' x| ≤ C * (|x| * tau ^ 2 + |x| ^ 3 * |tau| + x ^ 4) := by
    intro x hx hx2
    have h := hRval tau (sgn * x) hetar (hwin_le x hx hx2)
    have hx4 : (sgn * x) ^ 4 = x ^ 4 := by
      rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq sgn, hsgn2]; ring
    rw [abs_mul, hsgnabs, one_mul] at h ⊢
    rwa [hx4] at h
  have hR'c : ContinuousOn R' (Set.Icc (Real.sqrt (t / 2)) (Real.sqrt (2 * t))) := by
    intro x hx
    have hx0 : 0 < x := (Real.sqrt_pos.mpr (by
      have := amplitude_sq_pos alpha beta tau halpha hside; positivity)).trans_le hx.1
    have hx2 : x ^ 2 ≤ 2 * t := by
      have h2 : 0 ≤ 2 * t := by
        have := amplitude_sq_pos alpha beta tau halpha hside; positivity
      calc x ^ 2 ≤ Real.sqrt (2 * t) ^ 2 := pow_le_pow_left₀ hx0.le hx.2 2
        _ = 2 * t := Real.sq_sqrt h2
    have hca : ContinuousAt (R tau) (sgn * x) :=
      (hRder tau (sgn * x) hetar (hwin_le x hx0 hx2)).continuousAt
    have : ContinuousAt R' x :=
      continuousAt_const.mul (hca.comp (continuousAt_const.mul continuousAt_id))
    exact this.continuousWithinAt
  obtain ⟨x, hx0, -, hx2, hxroot⟩ :=
    exists_pos_equilibrium alpha beta tau C R' halpha hside hC hR'c hR'b hwin
  refine ⟨sgn * x, by rw [← mul_assoc, hsgn2, one_mul]; exact hx0, ?_, ?_⟩
  · -- the root in the original coordinate
    have hfield : pitchforkField alpha beta R tau (sgn * x) =
        sgn * (alpha * tau * x - beta * x ^ 3 + R' x) := by
      simp only [pitchforkField, hR'def]
      have h3 : (sgn * x) ^ 3 = sgn * x ^ 3 := by
        rw [mul_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq sgn, hsgn2]; ring
      rw [h3]
      linear_combination (-(R tau (sgn * x))) * hsgn2
    rw [hfield, hxroot, mul_zero]
  · set z := sgn * x with hsdef
    have hs0 : z ≠ 0 := by
      rw [hsdef]; exact mul_ne_zero (by rcases hsgn with rfl | rfl <;> norm_num) hx0.ne'
    have hsabs : |z| = x := by rw [hsdef, abs_mul, hsgnabs, one_mul, abs_of_pos hx0]
    have hsr : |z| ≤ r := hwin_le x hx0 hx2
    have hs1 : |z| ≤ 1 := hsr.trans hr1
    have hroot : alpha * tau * z - beta * z ^ 3 + R tau z = 0 := by
      have hfield : pitchforkField alpha beta R tau z = 0 := by
        simp only [pitchforkField, hsdef, hR'def] at hxroot ⊢
        have h3 : (sgn * x) ^ 3 = sgn * x ^ 3 := by
          rw [mul_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq sgn, hsgn2]; ring
        rw [h3]
        linear_combination sgn * hxroot + (-(R tau (sgn * x))) * hsgn2
      simpa [pitchforkField] using hfield
    have hd := pitchforkField_hasDerivAt alpha beta R Rs tau z (hRder tau z hetar hsr)
    have hsx : |z| ≤ Real.sqrt (2 * t) := by
      rw [hsabs]
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
        _ ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt hx2
    have hK := absorbedConst_nonneg alpha beta C halpha hC
    have hrect' : absorbedConst alpha beta C * (|tau| + |z|) ≤ |beta| / 2 :=
      (mul_le_mul_of_nonneg_left (by linarith) hK).trans hrect
    obtain ⟨-, hsign, hamp⟩ := equilibrium_core alpha beta tau z (R tau z) (Rs tau z)
      (deriv (pitchforkField alpha beta R tau) z) C halpha hbeta hs0 hC hs1 (hetar.trans hr1) hetaC
      hroot hd.deriv (hRval tau z hetar hsr) (hRs tau z hetar hsr) hrect'
    exact ⟨hamp, hsign⟩

/-- **Existence of the pitchfork branches.** Under the weak remainder bounds,
for all small `tau` on the side `tau * beta > 0` there are nontrivial zeros of both signs
with amplitude `√(alpha * tau / beta) + O(|tau|)` and `(∂_z field) * beta < 0`. -/
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
        pitchforkField alpha beta R tau z = 0 ∧
        abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (pitchforkField alpha beta R tau) z * beta < 0 := by
  filter_upwards [branchSmall_eventually alpha beta C r halpha hbeta hr] with tau hsmall hside
  exact exists_branch_at alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall
    hside

/-- **Side condition.** Near `(tau, z) = (0, 0)` every nontrivial zero of the
pitchfork field lies on the side `tau * beta > 0`, and the derivative there has sign
opposite to `beta`. -/
theorem branch_side_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), p.2 ≠ 0 →
      pitchforkField alpha beta R p.1 p.2 = 0 →
        0 < p.1 * beta ∧ deriv (pitchforkField alpha beta R p.1) p.2 * beta < 0 := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have c1 : Continuous fun p : ℝ × ℝ => |p.1| := by fun_prop
  have c2 : Continuous fun p : ℝ × ℝ => |p.2| := by fun_prop
  have c3 : Continuous fun p : ℝ × ℝ => 2 * C * |p.1| := by fun_prop
  have c4 : Continuous fun p : ℝ × ℝ => absorbedConst alpha beta C * (|p.1| + |p.2|) := by
    fun_prop
  have e1 := (c1.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := r)) (by simpa using hr)
  have e2 := (c2.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := r)) (by simpa using hr)
  have e3 := (c3.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := alpha))
    (by simpa using halpha)
  have e4 := (c4.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := |beta| / 2))
    (by simpa using half_pos hb)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4 hs0 hroot
  have hd := pitchforkField_hasDerivAt alpha beta R Rs p.1 p.2 (hRder p.1 p.2 h1.le h2.le)
  obtain ⟨hside, hsign, -⟩ := equilibrium_core alpha beta p.1 p.2 (R p.1 p.2)
    (Rs p.1 p.2) (deriv (pitchforkField alpha beta R p.1) p.2) C halpha hbeta hs0 hC
    (h2.le.trans hr1) (h1.le.trans hr1) h3.le (by simpa [pitchforkField] using hroot) hd.deriv
    (hRval p.1 p.2 h1.le h2.le) (hRs p.1 p.2 h1.le h2.le) h4.le
  exact ⟨hside, hsign⟩

end ScalarPitchfork
