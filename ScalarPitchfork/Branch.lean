/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Existence

/-!
# Uniqueness and continuity of the pitchfork branches

Under the remainder hypotheses of `ScalarPitchfork.Existence` (value bound, derivative and
derivative bound on the box `|tau|, |z| ≤ r ≤ 1`), this file proves:

* `root_localize`: in a fixed window `0 < |z| ≤ ρ` (`ρ = branchRadius`), every nontrivial
  zero lies on the side `tau * beta > 0` and satisfies
  `|z| ∈ [7/8 √(alpha tau / beta), 9/8 √(alpha tau / beta)]`;
* `scaled_field_strictAntiOn`: on the amplitude window
  `z ^ 2 ∈ [alpha tau / (2 beta), 2 alpha tau / beta]` the field is strictly monotone;
* `branchRoot_existsUnique`, `existsUnique_branchRoot_eventually`: the positive and the
  negative nontrivial zero in the window are unique;
* `small_zero_eq_branch`: these two zeros are the only small nontrivial zeros;
* `branch_continuousOn`, `branch_tendsto_zero`: the branch functions `tau ↦ z^±(tau)` are
  continuous on a neighbourhood of `0`, vanish off the side `tau * beta > 0`, and tend to
  `0` as `tau → 0`.

The results are packaged in `pitchfork_branch_curves`. Continuity needs one extra
hypothesis: for each fixed small `z`, the map `tau ↦ R tau z` is continuous. The size
bounds alone do not control the dependence of `R` on `tau`, and without it the zeros could
jump. No continuity of the derivative remainder is needed.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

open Filter Topology

/-- The `O(|tau|)` amplitude constant of `equilibrium_core`. -/
noncomputable def ampErr (alpha beta C : ℝ) : ℝ :=
  2 * alpha * absorbedConst alpha beta C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2

/-- The fixed radius of the uniqueness window in `z`. -/
noncomputable def branchRadius (alpha beta C r : ℝ) : ℝ :=
  min r (|beta| / (4 * (absorbedConst alpha beta C + 1)))

/-- Strict smallness conditions on `tau`; they define an open neighbourhood of `0`. -/
def BranchNhd (alpha beta C r tau : ℝ) : Prop :=
  |tau| < r ∧ 2 * C * |tau| < alpha ∧
    2 * (alpha * tau / beta) < branchRadius alpha beta C r ^ 2 ∧
    C * (|tau| + 2 * (alpha * tau / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2 ∧
    absorbedConst alpha beta C * (|tau| + Real.sqrt (2 * (alpha * tau / beta))) < |beta| / 2 ∧
    absorbedConst alpha beta C * |tau| < |beta| / 4 ∧
    64 * ampErr alpha beta C ^ 2 * |tau| < alpha / |beta|

/-- `z` is a nontrivial zero of sign `sgn` in the window `|z| ≤ rho`. -/
def BranchRoot (alpha beta rho : ℝ) (R : ℝ → ℝ → ℝ) (sgn tau z : ℝ) : Prop :=
  0 < sgn * z ∧ |z| ≤ rho ∧ pitchforkField alpha beta R tau z = 0

/-- The branch function `tau ↦ z^±(tau)`: the zero of sign `sgn` in the window if there
is one, and `0` otherwise. -/
noncomputable def branch (alpha beta rho : ℝ) (R : ℝ → ℝ → ℝ) (sgn tau : ℝ) : ℝ := by
  classical
  exact if h : ∃ z, BranchRoot alpha beta rho R sgn tau z then h.choose else 0

/-- The field in the coordinate `x = sgn * z`, multiplied by `sgn * beta`; on the
amplitude window it is strictly decreasing in `x`. -/
def scaledField (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (sgn tau x : ℝ) : ℝ :=
  sgn * beta * pitchforkField alpha beta R tau (sgn * x)

/-! ## Elementary facts -/

theorem abs_eq_sgn_mul (sgn u : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (h : 0 < sgn * u) :
    |u| = sgn * u := by
  rcases hsgn with rfl | rfl
  · rw [one_mul] at h ⊢; exact abs_of_pos h
  · have hu : u < 0 := by linarith
    rw [abs_of_neg hu]; ring

theorem ampErr_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ ampErr alpha beta C := by
  unfold ampErr
  have := absorbedConst_nonneg alpha beta C halpha hC
  positivity

theorem branchRadius_pos (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : 0 < branchRadius alpha beta C r := by
  have := absorbedConst_nonneg alpha beta C halpha hC
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  exact lt_min hr (by positivity)

theorem branchRadius_le (alpha beta C r : ℝ) : branchRadius alpha beta C r ≤ r :=
  min_le_left _ _

theorem absorbed_mul_radius (alpha beta C r : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    absorbedConst alpha beta C * branchRadius alpha beta C r ≤ |beta| / 4 := by
  have hK := absorbedConst_nonneg alpha beta C halpha hC
  have hρ : branchRadius alpha beta C r ≤ |beta| / (4 * (absorbedConst alpha beta C + 1)) :=
    min_le_right _ _
  calc absorbedConst alpha beta C * branchRadius alpha beta C r
      ≤ absorbedConst alpha beta C * (|beta| / (4 * (absorbedConst alpha beta C + 1))) :=
        mul_le_mul_of_nonneg_left hρ hK
    _ ≤ |beta| / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg beta]

theorem branchNhd_branchSmall (alpha beta C r tau : ℝ) (halpha : 0 < alpha)
    (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr : 0 < r)
    (h : BranchNhd alpha beta C r tau) : BranchSmall alpha beta C r tau := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := h
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have hρr : branchRadius alpha beta C r ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ hρ.le (branchRadius_le alpha beta C r) 2
  exact ⟨h1.le, h2.le, (h3.trans_le hρr).le, h4, h5.le⟩

/-- On the side `tau * beta > 0`, smallness gives `8 * ampErr * |tau| ≤ √(alpha tau / beta)`. -/
theorem amp_err_le_sqrt (alpha beta C r tau : ℝ) (halpha : 0 < alpha)
    (hC : 0 ≤ C) (hside : 0 < tau * beta) (h : BranchNhd alpha beta C r tau) :
    8 * ampErr alpha beta C * |tau| ≤ Real.sqrt (alpha * tau / beta) := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := h
  have hb : 0 < |beta| := abs_pos.mpr (by rintro rfl; simp at hside)
  have hE := ampErr_nonneg alpha beta C halpha hC
  rw [Real.le_sqrt (by positivity) (amplitude_sq_pos alpha beta tau halpha hside).le,
    amp_sq_eq_abs alpha beta tau hside, le_div_iff₀ hb]
  rw [lt_div_iff₀ hb] at h7
  have he := abs_nonneg tau
  have : 64 * ampErr alpha beta C ^ 2 * |tau| * |beta| * |tau| ≤ alpha * |tau| :=
    mul_le_mul_of_nonneg_right h7.le he
  nlinarith

/-- Points with `x ∈ [13/16, 19/16] * √t` lie in the amplitude window. -/
theorem mem_window (t x : ℝ) (ht : 0 < t)
    (h1 : 13 / 16 * Real.sqrt t ≤ x) (h2 : x ≤ 19 / 16 * Real.sqrt t) :
    x ∈ Set.Icc (Real.sqrt (t / 2)) (Real.sqrt (2 * t)) := by
  have hs := Real.sq_sqrt ht.le
  have hs0 := Real.sqrt_nonneg t
  have hx : 0 ≤ x := le_trans (by positivity) h1
  constructor
  · rw [Real.sqrt_le_left hx]
    nlinarith
  · rw [Real.le_sqrt hx (by positivity)]
    nlinarith

/-! ## Localization of every small nontrivial zero -/

/-- Every nontrivial zero in the window `|z| ≤ ρ` lies on the side `tau * beta > 0`
and has `|z| ∈ [7/8, 9/8] * √(alpha tau / beta)`. -/
theorem root_localize (alpha beta C r tau z : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hs : z ≠ 0)
    (hsρ : |z| ≤ branchRadius alpha beta C r)
    (hroot : pitchforkField alpha beta R tau z = 0) :
    0 < tau * beta ∧ 7 / 8 * Real.sqrt (alpha * tau / beta) ≤ |z| ∧
      |z| ≤ 9 / 8 * Real.sqrt (alpha * tau / beta) := by
  have hsmall' := hsmall
  obtain ⟨h1, h2, -, -, -, h6, -⟩ := hsmall
  have hsr : |z| ≤ r := hsρ.trans (branchRadius_le alpha beta C r)
  have hK := absorbedConst_nonneg alpha beta C halpha hC
  have hrect : absorbedConst alpha beta C * (|tau| + |z|) ≤ |beta| / 2 := by
    have h1' := absorbed_mul_radius alpha beta C r halpha hC
    have h2' : absorbedConst alpha beta C * |z| ≤
        absorbedConst alpha beta C * branchRadius alpha beta C r :=
      mul_le_mul_of_nonneg_left hsρ hK
    rw [mul_add]
    linarith
  obtain ⟨hside, -, hamp⟩ := equilibrium_core alpha beta tau z (R tau z) (Rs tau z)
    (alpha * tau - 3 * beta * z ^ 2 + Rs tau z) C halpha hbeta hs hC (hsr.trans hr1)
    (h1.le.trans hr1) h2.le (by simpa [pitchforkField] using hroot) rfl
    (hRval tau z h1.le hsr) (hRs tau z h1.le hsr) hrect
  have h8 := amp_err_le_sqrt alpha beta C r tau halpha hC hside hsmall'
  have hamp' : abs (|z| - Real.sqrt (alpha * tau / beta)) ≤ ampErr alpha beta C * |tau| :=
    hamp
  obtain ⟨ha, hb⟩ := abs_le.mp hamp'
  refine ⟨hside, ?_, ?_⟩ <;> nlinarith

/-! ## Strict monotonicity on the amplitude window -/

/-- On the amplitude window the derivative of the field has the sign of `-beta`. -/
theorem field_deriv_neg_on_window (alpha beta C tau x Rs : ℝ)
    (hside : 0 < tau * beta) (hC : 0 ≤ C) (hx : 0 < x)
    (hx1 : alpha * tau / beta / 2 ≤ x ^ 2) (hx2 : x ^ 2 ≤ 2 * (alpha * tau / beta))
    (hRs : |Rs| ≤ C * (tau ^ 2 + x ^ 2 * |tau| + |x| ^ 3))
    (hwin : C * (|tau| + 2 * (alpha * tau / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2) :
    beta * (alpha * tau - 3 * beta * x ^ 2 + Rs) < 0 := by
  have hbeta : beta ≠ 0 := by rintro rfl; simp at hside
  have hxR : |x * Rs| ≤ C * (|x| * tau ^ 2 + |x| ^ 3 * |tau| + x ^ 4) := by
    have hxa : |x| = x := abs_of_pos hx
    rw [hxa] at hRs
    rw [abs_mul, hxa]
    calc x * |Rs| ≤ x * (C * (tau ^ 2 + x ^ 2 * |tau| + x ^ 3)) :=
          mul_le_mul_of_nonneg_left hRs hx.le
      _ = C * (x * tau ^ 2 + x ^ 3 * |tau| + x ^ 4) := by ring
  have hlt := weak_value_lt_on_window alpha beta tau x (x * Rs) C hside hC hx hx2 hxR hwin
  rw [abs_mul, abs_of_pos hx] at hlt
  have hRs' : |Rs| < alpha / 2 * |tau| := lt_of_mul_lt_mul_left hlt hx.le
  have hbt : beta * (alpha * tau / beta) = alpha * tau := by field_simp
  have hb2 : beta ^ 2 * (alpha * tau / beta / 2) ≤ beta ^ 2 * x ^ 2 :=
    mul_le_mul_of_nonneg_left hx1 (sq_nonneg beta)
  have hb2' : beta ^ 2 * (alpha * tau / beta / 2) = alpha * (tau * beta) / 2 := by
    field_simp
  have habs : |beta| * |tau| = tau * beta := by
    rw [← abs_mul, mul_comm, abs_of_pos hside]
  have hbR : beta * Rs ≤ |beta| * |Rs| := by rw [← abs_mul]; exact le_abs_self _
  have hbR' : |beta| * |Rs| < |beta| * (alpha / 2 * |tau|) :=
    mul_lt_mul_of_pos_left hRs' (abs_pos.mpr hbeta)
  have hexp : beta * (alpha * tau - 3 * beta * x ^ 2 + Rs) =
      alpha * (tau * beta) - 3 * (beta ^ 2 * x ^ 2) + beta * Rs := by ring
  rw [hexp]
  have : |beta| * (alpha / 2 * |tau|) = alpha * (tau * beta) / 2 := by
    rw [← habs]; ring
  linarith

/-- The derivative of the field in the coordinate `x = sgn * z`, multiplied by `sgn * beta`. -/
theorem scaled_field_hasDerivAt (alpha beta : ℝ) (R Rs : ℝ → ℝ → ℝ) (sgn tau x : ℝ)
    (hd : HasDerivAt (R tau) (Rs tau (sgn * x)) (sgn * x)) :
    HasDerivAt (scaledField alpha beta R sgn tau)
      (sgn * beta * ((alpha * tau - 3 * beta * (sgn * x) ^ 2 + Rs tau (sgn * x)) * sgn)) x := by
  have hf := pitchforkField_hasDerivAt alpha beta R Rs tau (sgn * x) hd
  have hm : HasDerivAt (fun y : ℝ => sgn * y) sgn x := by
    simpa using (hasDerivAt_id x).const_mul sgn
  exact (hf.comp x hm).const_mul (sgn * beta)

/-- Strict monotonicity of the scaled field on the amplitude window. -/
theorem scaled_field_strictAntiOn (alpha beta C r tau sgn : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchSmall alpha beta C r tau) (hside : 0 < tau * beta)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    StrictAntiOn (scaledField alpha beta R sgn tau)
      (Set.Icc (Real.sqrt (alpha * tau / beta / 2)) (Real.sqrt (2 * (alpha * tau / beta)))) := by
  obtain ⟨hetar, -, h2t, hwin, -⟩ := hsmall
  have ht := amplitude_sq_pos alpha beta tau halpha hside
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsabs (x : ℝ) : |sgn * x| = |x| := by rcases hsgn with rfl | rfl <;> simp
  have hssq (x : ℝ) : (sgn * x) ^ 2 = x ^ 2 := by rcases hsgn with rfl | rfl <;> ring
  -- facts on the window
  have hwinfacts : ∀ x ∈ Set.Icc (Real.sqrt (alpha * tau / beta / 2))
      (Real.sqrt (2 * (alpha * tau / beta))),
      0 < x ∧ alpha * tau / beta / 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 2 * (alpha * tau / beta) ∧
        |sgn * x| ≤ r := by
    intro x hx
    have hx0 : 0 < x := (Real.sqrt_pos.mpr (by positivity)).trans_le hx.1
    have hlo : alpha * tau / beta / 2 ≤ x ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx.1 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hhi : x ^ 2 ≤ 2 * (alpha * tau / beta) := by
      have := pow_le_pow_left₀ hx0.le hx.2 2
      rwa [Real.sq_sqrt (by positivity)] at this
    refine ⟨hx0, hlo, hhi, ?_⟩
    rw [hsabs, abs_of_pos hx0]
    have hr0 : 0 ≤ r := (abs_nonneg _).trans hetar
    nlinarith
  have hder : ∀ x ∈ Set.Icc (Real.sqrt (alpha * tau / beta / 2))
      (Real.sqrt (2 * (alpha * tau / beta))),
      HasDerivAt (scaledField alpha beta R sgn tau)
        (beta * (alpha * tau - 3 * beta * x ^ 2 + Rs tau (sgn * x))) x := by
    intro x hx
    obtain ⟨-, -, -, hxr⟩ := hwinfacts x hx
    have h := scaled_field_hasDerivAt alpha beta R Rs sgn tau x (hRder tau _ hetar hxr)
    convert h using 1
    rw [hssq]
    linear_combination (-(beta * (alpha * tau - 3 * beta * x ^ 2 + Rs tau (sgn * x)))) * hsq
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hder x hx').deriv]
    obtain ⟨hx0, hlo, hhi, hxr⟩ := hwinfacts x hx'
    have hb := hRs tau (sgn * x) hetar hxr
    rw [hssq, hsabs] at hb
    exact field_deriv_neg_on_window alpha beta C tau x _ hside hC hx0 hlo hhi hb hwin

/-! ## The neighbourhood of `tau = 0` -/

theorem isOpen_branchNhd (alpha beta C r : ℝ) :
    IsOpen {tau | BranchNhd alpha beta C r tau} := by
  simp only [BranchNhd, Set.ofPred_and]
  refine IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_)
    (IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_)
    (IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_) (isOpen_lt ?_ ?_)))))) <;>
    fun_prop

theorem branchNhd_zero (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : BranchNhd alpha beta C r 0 := by
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  refine ⟨by simpa using hr, by simpa using halpha, by simpa using pow_pos hρ 2,
    by simpa using half_pos halpha, by simpa using half_pos hb, by simpa using hb,
    by simpa using div_pos halpha hb⟩

theorem branchNhd_mem_nhds (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : {tau | BranchNhd alpha beta C r tau} ∈ 𝓝 (0 : ℝ) :=
  (isOpen_branchNhd alpha beta C r).mem_nhds (branchNhd_zero alpha beta C r halpha hbeta hC hr)

/-! ## Existence and uniqueness of the zero of each sign -/

/-- Existence of the zero of sign `sgn` in the window, with amplitude and derivative
sign (from `exists_branch_at`). -/
theorem branch_root_exists (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : 0 < tau * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ∃ z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z ∧
      abs (|z| - Real.sqrt (alpha * tau / beta)) ≤ ampErr alpha beta C * |tau| ∧
      deriv (pitchforkField alpha beta R tau) z * beta < 0 := by
  obtain ⟨z, hs0, hroot, hamp, hder⟩ := exists_branch_at alpha beta C r tau R Rs halpha hbeta
    hC hr hr1 hRval hRder hRs
    (branchNhd_branchSmall alpha beta C r tau halpha hbeta hC hr hsmall) hside sgn hsgn
  have h8 := amp_err_le_sqrt alpha beta C r tau halpha hC hside hsmall
  have hamp' : abs (|z| - Real.sqrt (alpha * tau / beta)) ≤ ampErr alpha beta C * |tau| :=
    hamp
  refine ⟨z, ⟨hs0, ?_, hroot⟩, hamp', hder⟩
  obtain ⟨-, hb⟩ := abs_le.mp hamp'
  have ht := amplitude_sq_pos alpha beta tau halpha hside
  have hsq0 := Real.sqrt_nonneg (alpha * tau / beta)
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  obtain ⟨-, -, h3, -⟩ := hsmall
  have hw := mem_window (alpha * tau / beta) (9 / 8 * Real.sqrt (alpha * tau / beta)) ht
    (by linarith) (by linarith)
  have h2 : Real.sqrt (2 * (alpha * tau / beta)) < branchRadius alpha beta C r :=
    (Real.sqrt_lt' hρ).mpr h3
  linarith [hw.2]

/-- Uniqueness of the zero of sign `sgn` in the window `0 < sgn * z`, `|z| ≤ ρ`. -/
theorem branchRoot_unique (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : 0 < tau * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) {z z' : ℝ}
    (hs : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z)
    (hs' : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z') :
    z = z' := by
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgn0 : sgn ≠ 0 := by rcases hsgn with rfl | rfl <;> norm_num
  have ht := amplitude_sq_pos alpha beta tau halpha hside
  have hsq0 := Real.sqrt_nonneg (alpha * tau / beta)
  have key : ∀ u, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau u →
      sgn * u ∈ Set.Icc (Real.sqrt (alpha * tau / beta / 2))
        (Real.sqrt (2 * (alpha * tau / beta))) ∧
      scaledField alpha beta R sgn tau (sgn * u) = 0 := by
    intro u ⟨hu0, huρ, hur⟩
    have hu : u ≠ 0 := by rintro rfl; simp at hu0
    obtain ⟨-, hlo, hhi⟩ := root_localize alpha beta C r tau u R Rs halpha hbeta hC hr1
      hRval hRs hsmall hu huρ hur
    rw [abs_eq_sgn_mul sgn u hsgn hu0] at hlo hhi
    have hw := mem_window (alpha * tau / beta) (sgn * u) ht (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · exact hw
    · unfold scaledField
      rw [← mul_assoc, hsq, one_mul, hur, mul_zero]
  obtain ⟨hx, hFx⟩ := key z hs
  obtain ⟨hx', hFx'⟩ := key z' hs'
  have hanti := scaled_field_strictAntiOn alpha beta C r tau sgn R Rs halpha hC hRder hRs
    (branchNhd_branchSmall alpha beta C r tau halpha hbeta hC hr hsmall) hside hsgn
  exact mul_left_cancel₀ hsgn0 (hanti.injOn hx hx' (hFx.trans hFx'.symm))

/-- **Uniqueness.** On the side `tau * beta > 0` there is exactly one zero of each
sign in the fixed window `|z| ≤ ρ`. -/
theorem branchRoot_existsUnique (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : 0 < tau * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ∃! z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z := by
  obtain ⟨z, hs, -, -⟩ := branch_root_exists alpha beta C r tau R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside sgn hsgn
  exact ⟨z, hs, fun y hy => branchRoot_unique alpha beta C r tau R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside sgn hsgn hy hs⟩

/-- **Local uniqueness of the two branches.** On a fixed window `|z| ≤ ρ`, with `ρ`
independent of `tau`, for each small `tau` on the side `tau * beta > 0` there is exactly
one zero of each sign of the perturbed pitchfork field
`alpha * tau * z - beta * z ^ 3 + R tau z`. Here `ρ = branchRadius alpha beta C r` and the
neighbourhood of `0` is `{tau | BranchNhd alpha beta C r tau}`; this restates
`branchRoot_existsUnique` with `BranchRoot` and `pitchforkField` unfolded. -/
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
  refine ⟨branchRadius alpha beta C r, branchRadius_pos alpha beta C r halpha hbeta hC hr, ?_⟩
  filter_upwards [branchNhd_mem_nhds alpha beta C r halpha hbeta hC hr] with tau hsmall
  intro hside sgn hsgn
  exact branchRoot_existsUnique alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    hsmall hside sgn hsgn

/-! ## The branch functions -/

/-- The branch value is the zero of sign `sgn`, with the amplitude estimate and the
derivative sign. -/
theorem branch_spec (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : 0 < tau * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau
        (branch alpha beta (branchRadius alpha beta C r) R sgn tau) ∧
      abs (|branch alpha beta (branchRadius alpha beta C r) R sgn tau| -
          Real.sqrt (alpha * tau / beta)) ≤ ampErr alpha beta C * |tau| ∧
      deriv (pitchforkField alpha beta R tau)
          (branch alpha beta (branchRadius alpha beta C r) R sgn tau) * beta < 0 := by
  obtain ⟨z, hs, hamp, hder⟩ := branch_root_exists alpha beta C r tau R Rs halpha hbeta hC
    hr hr1 hRval hRder hRs hsmall hside sgn hsgn
  have hex : ∃ z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z := ⟨z, hs⟩
  have hb : branch alpha beta (branchRadius alpha beta C r) R sgn tau = z := by
    have hc : branch alpha beta (branchRadius alpha beta C r) R sgn tau = hex.choose := by
      unfold branch
      rw [dite_eq_left hex]
    rw [hc]
    exact branchRoot_unique alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside sgn hsgn hex.choose_spec hs
  rw [hb]
  exact ⟨hs, hamp, hder⟩

/-- A zero of sign `sgn` in the window is the branch value. -/
theorem branch_eq_of_root (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : 0 < tau * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) {z : ℝ}
    (hs : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z) :
    branch alpha beta (branchRadius alpha beta C r) R sgn tau = z :=
  branchRoot_unique alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall hside
    sgn hsgn (branch_spec alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall
      hside sgn hsgn).1 hs

/-- Off the side `tau * beta > 0` there is no nontrivial small zero, so the branch
function is `0` there (in particular at `tau = 0`). -/
theorem branch_eq_zero_of_not_side (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hside : tau * beta ≤ 0) (sgn : ℝ) :
    branch alpha beta (branchRadius alpha beta C r) R sgn tau = 0 := by
  have hne : ¬ ∃ z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z := by
    rintro ⟨z, hs0, hsρ, hroot⟩
    have hs : z ≠ 0 := by rintro rfl; simp at hs0
    exact absurd (root_localize alpha beta C r tau z R Rs halpha hbeta hC hr1 hRval hRs
      hsmall hs hsρ hroot).1 (not_lt.mpr hside)
  unfold branch
  rw [dite_eq_right hne]

/-- **Classification.** Every small nontrivial zero lies on the side
`tau * beta > 0` and is one of the two branch values. -/
theorem small_zero_eq_branch (alpha beta C r tau z : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (hs : z ≠ 0)
    (hsρ : |z| ≤ branchRadius alpha beta C r)
    (hroot : pitchforkField alpha beta R tau z = 0) :
    0 < tau * beta ∧
      (z = branch alpha beta (branchRadius alpha beta C r) R 1 tau ∨
        z = branch alpha beta (branchRadius alpha beta C r) R (-1) tau) := by
  have hside := (root_localize alpha beta C r tau z R Rs halpha hbeta hC hr1 hRval hRs hsmall
    hs hsρ hroot).1
  refine ⟨hside, ?_⟩
  rcases lt_or_gt_of_ne hs with h | h
  · right
    exact (branch_eq_of_root alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside (-1) (Or.inr rfl) ⟨by linarith, hsρ, hroot⟩).symm
  · left
    exact (branch_eq_of_root alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside 1 (Or.inl rfl) ⟨by linarith, hsρ, hroot⟩).symm

/-- The branch functions are bounded by `9/8 * √(alpha tau / beta)` on the whole
neighbourhood (and vanish off the side). -/
theorem branch_abs_le (alpha beta C r tau : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hsmall : BranchNhd alpha beta C r tau) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    |branch alpha beta (branchRadius alpha beta C r) R sgn tau| ≤
      9 / 8 * Real.sqrt (alpha * tau / beta) := by
  rcases lt_or_ge 0 (tau * beta) with hside | hside
  · obtain ⟨⟨hpos, hρ, hroot⟩, -, -⟩ := branch_spec alpha beta C r tau R Rs halpha hbeta hC hr
      hr1 hRval hRder hRs hsmall hside sgn hsgn
    have hne : branch alpha beta (branchRadius alpha beta C r) R sgn tau ≠ 0 := by
      intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    exact (root_localize alpha beta C r tau _ R Rs halpha hbeta hC hr1 hRval hRs hsmall hne hρ
      hroot).2.2
  · rw [branch_eq_zero_of_not_side alpha beta C r tau R Rs halpha hbeta hC hr1 hRval hRs hsmall
      hside sgn, abs_zero]
    positivity

/-! ## Continuity of the branch functions -/

/-- Continuity of the scaled field in the parameter, from continuity of the remainder. -/
theorem scaledField_continuousAt_eta (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (sgn y tau0 : ℝ)
    (h : ContinuousAt (fun e => R e (sgn * y)) tau0) :
    ContinuousAt (fun e => scaledField alpha beta R sgn e y) tau0 := by
  unfold scaledField pitchforkField
  fun_prop

/-- Continuity of the branch function at a point on the side `tau * beta > 0`. The
only input beyond the value and derivative bounds is `hRcont`: continuity of
`tau ↦ R tau z` for each fixed small `z`. -/
theorem branch_continuousAt_side (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (tau0 : ℝ)
    (hsmall0 : BranchNhd alpha beta C r tau0) (hside0 : 0 < tau0 * beta) :
    ContinuousAt (branch alpha beta (branchRadius alpha beta C r) R sgn) tau0 := by
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgn0 : sgn ≠ 0 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsabs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have ht0 := amplitude_sq_pos alpha beta tau0 halpha hside0
  have hsqrt0 : 0 < Real.sqrt (alpha * tau0 / beta) := Real.sqrt_pos.mpr ht0
  obtain ⟨⟨hpos0, hρ0, hroot0⟩, -, -⟩ := branch_spec alpha beta C r tau0 R Rs halpha hbeta hC
    hr hr1 hRval hRder hRs hsmall0 hside0 sgn hsgn
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 = branch alpha beta (branchRadius alpha beta C r) R sgn tau0 :=
    ⟨_, rfl⟩
  rw [← hb0] at hpos0 hρ0 hroot0
  have hb0ne : b0 ≠ 0 := by intro h; rw [h, mul_zero] at hpos0; exact lt_irrefl _ hpos0
  obtain ⟨-, hlo, hhi⟩ := root_localize alpha beta C r tau0 b0 R Rs halpha hbeta hC hr1 hRval
    hRs hsmall0 hb0ne hρ0 hroot0
  rw [abs_eq_sgn_mul sgn b0 hsgn hpos0] at hlo hhi
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = sgn * b0 := ⟨_, rfl⟩
  rw [← hx0] at hlo hhi
  have hbx : b0 = sgn * x0 := by rw [hx0, ← mul_assoc, hsq, one_mul]
  have h2t0 : Real.sqrt (2 * (alpha * tau0 / beta)) < branchRadius alpha beta C r :=
    (Real.sqrt_lt' hρ).mpr hsmall0.2.2.1
  have hρr := branchRadius_le alpha beta C r
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = min (ε / 2) (Real.sqrt (alpha * tau0 / beta) / 16) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ Real.sqrt (alpha * tau0 / beta) / 16 := by rw [hδdef]; exact min_le_right _ _
  have hmemA := mem_window (alpha * tau0 / beta) (x0 - δ) ht0 (by linarith) (by linarith)
  have hmemC := mem_window (alpha * tau0 / beta) (x0 + δ) ht0 (by linarith) (by linarith)
  have hmem0 := mem_window (alpha * tau0 / beta) x0 ht0 (by linarith) (by linarith)
  have hwin : ∀ x ∈ Set.Icc (Real.sqrt (alpha * tau0 / beta / 2))
      (Real.sqrt (2 * (alpha * tau0 / beta))), |sgn * x| ≤ r := by
    intro x hx
    have hx0' : 0 ≤ x := (Real.sqrt_nonneg _).trans hx.1
    rw [abs_mul, hsabs, one_mul, abs_of_nonneg hx0']
    linarith [hx.2]
  have hanti := scaled_field_strictAntiOn alpha beta C r tau0 sgn R Rs halpha hC hRder hRs
    (branchNhd_branchSmall alpha beta C r tau0 halpha hbeta hC hr hsmall0) hside0 hsgn
  have hF0 : scaledField alpha beta R sgn tau0 x0 = 0 := by
    unfold scaledField
    rw [← hbx, hroot0, mul_zero]
  have hFa : 0 < scaledField alpha beta R sgn tau0 (x0 - δ) := by
    rw [← hF0]; exact hanti hmemA hmem0 (by linarith)
  have hFc : scaledField alpha beta R sgn tau0 (x0 + δ) < 0 := by
    rw [← hF0]; exact hanti hmem0 hmemC (by linarith)
  have htau0r : |tau0| < r := hsmall0.1
  have ev1 : ∀ᶠ tau in 𝓝 tau0, BranchNhd alpha beta C r tau :=
    (isOpen_branchNhd alpha beta C r).mem_nhds hsmall0
  have ev2 : ∀ᶠ tau in 𝓝 tau0, 0 < tau * beta :=
    (continuousAt_id.mul continuousAt_const : ContinuousAt (fun e : ℝ => e * beta) tau0).eventually
      (lt_mem_nhds hside0)
  have ev3 : ∀ᶠ tau in 𝓝 tau0, 0 < scaledField alpha beta R sgn tau (x0 - δ) :=
    (scaledField_continuousAt_eta alpha beta R sgn (x0 - δ) tau0
      (hRcont tau0 _ htau0r (hwin _ hmemA))).eventually (lt_mem_nhds hFa)
  have ev4 : ∀ᶠ tau in 𝓝 tau0, scaledField alpha beta R sgn tau (x0 + δ) < 0 :=
    (scaledField_continuousAt_eta alpha beta R sgn (x0 + δ) tau0
      (hRcont tau0 _ htau0r (hwin _ hmemC))).eventually (gt_mem_nhds hFc)
  filter_upwards [ev1, ev2, ev3, ev4] with tau hsm hsd hFa' hFc'
  have hsub : Set.Icc (x0 - δ) (x0 + δ) ⊆ Set.Icc (Real.sqrt (alpha * tau0 / beta / 2))
      (Real.sqrt (2 * (alpha * tau0 / beta))) :=
    fun y hy => ⟨hmemA.1.trans hy.1, hy.2.trans hmemC.2⟩
  have hcont : ContinuousOn (scaledField alpha beta R sgn tau) (Set.Icc (x0 - δ) (x0 + δ)) := by
    intro y hy
    exact (scaled_field_hasDerivAt alpha beta R Rs sgn tau y
      (hRder tau _ hsm.1.le (hwin y (hsub hy)))).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc' (by linarith) hcont ⟨hFc'.le, hFa'.le⟩
  have hy0 : 0 < y := by linarith [hy.1]
  have hroot : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau (sgn * y) := by
    refine ⟨by rw [← mul_assoc, hsq, one_mul]; exact hy0, ?_, ?_⟩
    · rw [abs_mul, hsabs, one_mul, abs_of_pos hy0]
      linarith [hy.2, hmemC.2]
    · unfold scaledField at hFy
      exact (mul_eq_zero.mp hFy).resolve_left (mul_ne_zero hsgn0 hbeta)
  rw [branch_eq_of_root alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsm hsd
    sgn hsgn hroot, ← hb0, hbx, Real.dist_eq, ← mul_sub, abs_mul, hsabs, one_mul, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- The branch functions vanish at `tau = 0`. -/
theorem branch_zero (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) (sgn : ℝ) :
    branch alpha beta (branchRadius alpha beta C r) R sgn 0 = 0 :=
  branch_eq_zero_of_not_side alpha beta C r 0 R Rs halpha hbeta hC hr1 hRval hRs
    (branchNhd_zero alpha beta C r halpha hbeta hC hr) (by simp) sgn

/-- **Through the origin**: `z^±(tau) → 0` as `tau → 0`. -/
theorem branch_tendsto_zero (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun tau : ℝ => 9 / 8 * Real.sqrt (alpha * tau / beta) := by fun_prop
  have hlim : Tendsto (fun tau : ℝ => 9 / 8 * Real.sqrt (alpha * tau / beta)) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  apply squeeze_zero_norm' _ hlim
  filter_upwards [branchNhd_mem_nhds alpha beta C r halpha hbeta hC hr] with tau h
  rw [Real.norm_eq_abs]
  exact branch_abs_le alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs h sgn hsgn

/-- **Continuity**: each branch function is continuous on the open neighbourhood
`{tau | BranchNhd tau}` of `0`. -/
theorem branch_continuousOn (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
      {tau | BranchNhd alpha beta C r tau} := by
  intro tau0 h0
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy (tau0 * beta) 0 with hneg | hzero | hpos
  · have ev : ∀ᶠ tau in 𝓝 tau0, BranchNhd alpha beta C r tau ∧ tau * beta < 0 :=
      Filter.Eventually.and ((isOpen_branchNhd alpha beta C r).mem_nhds h0)
        ((continuousAt_id.mul continuousAt_const :
          ContinuousAt (fun e : ℝ => e * beta) tau0).eventually (gt_mem_nhds hneg))
    have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 tau0]
        branch alpha beta (branchRadius alpha beta C r) R sgn :=
      ev.mono fun tau h => (branch_eq_zero_of_not_side alpha beta C r tau R Rs halpha hbeta hC
        hr1 hRval hRs h.1 h.2.le sgn).symm
    exact continuousAt_const.congr heq
  · have he : tau0 = 0 := (mul_eq_zero.mp hzero).resolve_right hbeta
    subst he
    rw [ContinuousAt, branch_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRs sgn]
    exact branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs sgn hsgn
  · exact branch_continuousAt_side alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hRcont sgn hsgn tau0 h0 hpos

/-! ## The packaged statement -/

/-- **The pitchfork branch curves.** Under the weak remainder bounds plus continuity
of `tau ↦ R tau z`, there are a window radius `ρ > 0` and an open neighbourhood of
`tau = 0` such that, for each sign `sgn = ±1`, the branch function `z^sgn(tau)`:
* is continuous on the neighbourhood, vanishes at `tau = 0`, and tends to `0` as `tau → 0`;
* vanishes for `tau` in the neighbourhood with `tau * beta ≤ 0`;
* for `tau` in the neighbourhood with `tau * beta > 0` is the unique zero of sign `sgn` in
  `|z| ≤ ρ`, with amplitude `√(alpha tau / beta) + O(|tau|)` and
  `(∂_z field) * beta < 0`;

and every nontrivial zero `0 < |z| ≤ ρ` at `tau` in the neighbourhood is one of
`z^±(tau)`. -/
theorem pitchfork_branch_curves (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) :
    0 < branchRadius alpha beta C r ∧ IsOpen {tau | BranchNhd alpha beta C r tau} ∧
      {tau | BranchNhd alpha beta C r tau} ∈ 𝓝 (0 : ℝ) ∧
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
            {tau | BranchNhd alpha beta C r tau} ∧
          branch alpha beta (branchRadius alpha beta C r) R sgn 0 = 0 ∧
          Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) ∧
          (∀ tau, BranchNhd alpha beta C r tau → tau * beta ≤ 0 →
            branch alpha beta (branchRadius alpha beta C r) R sgn tau = 0) ∧
          (∀ tau, BranchNhd alpha beta C r tau → 0 < tau * beta →
            (∃! z, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau z) ∧
            BranchRoot alpha beta (branchRadius alpha beta C r) R sgn tau
                (branch alpha beta (branchRadius alpha beta C r) R sgn tau) ∧
            abs (|branch alpha beta (branchRadius alpha beta C r) R sgn tau| -
                Real.sqrt (alpha * tau / beta)) ≤ ampErr alpha beta C * |tau| ∧
            deriv (pitchforkField alpha beta R tau)
                (branch alpha beta (branchRadius alpha beta C r) R sgn tau) * beta < 0)) ∧
      (∀ tau z, BranchNhd alpha beta C r tau → z ≠ 0 →
        |z| ≤ branchRadius alpha beta C r → pitchforkField alpha beta R tau z = 0 →
        0 < tau * beta ∧
          (z = branch alpha beta (branchRadius alpha beta C r) R 1 tau ∨
            z = branch alpha beta (branchRadius alpha beta C r) R (-1) tau)) := by
  refine ⟨branchRadius_pos alpha beta C r halpha hbeta hC hr, isOpen_branchNhd alpha beta C r,
    branchNhd_mem_nhds alpha beta C r halpha hbeta hC hr, fun sgn hsgn => ?_,
    fun tau z h hs hsρ hroot => small_zero_eq_branch alpha beta C r tau z R Rs halpha hbeta
      hC hr hr1 hRval hRder hRs h hs hsρ hroot⟩
  refine ⟨branch_continuousOn alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs hRcont
      sgn hsgn, branch_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRs sgn,
    branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs sgn hsgn,
    fun tau h hside => branch_eq_zero_of_not_side alpha beta C r tau R Rs halpha hbeta hC hr1
      hRval hRs h hside sgn, fun tau h hside => ?_⟩
  exact ⟨branchRoot_existsUnique alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    h hside sgn hsgn, branch_spec alpha beta C r tau R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    h hside sgn hsgn⟩

end ScalarPitchfork
