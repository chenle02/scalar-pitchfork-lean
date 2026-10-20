/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Branch

/-!
# Remainder bounds from smoothness and jets

The remainder hypotheses of `ScalarPitchfork.Existence` and `ScalarPitchfork.Branch`
follow from smoothness and finitely many jet conditions (`PitchforkJet`): the remainder
`R(tau, z)` is `C⁴` on an open set containing the box `|tau|, |z| ≤ r ≤ 1`, vanishes on
the axis `z = 0`, and at the origin
`∂_z R = ∂_tau ∂_z R = ∂_z² R = ∂_tau ∂_z² R = ∂_z³ R = 0`.

The proof applies the one-variable mean value inequality along the segments
`t ↦ (tau, t)` and `t ↦ (t, 0)`, with uniform bounds on the third and fourth derivatives
from compactness of the box (`remainderBounds_of_jet`).

The stronger bound of `ScalarPitchfork.StrongRemainder` holds under the same hypotheses
if and only if the axis condition `∂_z R(tau, 0) = 0` holds on the box
(`strongBound_iff_axis`); the jets at the origin do not imply it
(`ScalarPitchfork.jet_not_sufficient_for_strongBound`). The corollaries
`exists_branch_eventually_of_jet` and `pitchfork_branch_curves_of_jet` derive the branch
theorems from the jet hypotheses alone. The coordinate directions are `eTau = (1, 0)`
(parameter) and `eZ = (0, 1)` (amplitude).
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

open Filter Topology

/-! ## Directions, mean value steps and line derivatives -/

/-- The parameter direction `(1, 0)` in `ℝ × ℝ`. -/
def eTau : ℝ × ℝ := (1, 0)

/-- The amplitude direction `(0, 1)` in `ℝ × ℝ`. -/
def eZ : ℝ × ℝ := (0, 1)

theorem norm_eTau : ‖eTau‖ = 1 := by simp [eTau, Prod.norm_def]

theorem norm_eZ : ‖eZ‖ = 1 := by simp [eZ, Prod.norm_def]

theorem mem_box (r e z : ℝ) : ((e, z) : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) r ↔
    |e| ≤ r ∧ |z| ≤ r := by
  simp [Prod.norm_def, Real.norm_eq_abs]

/-- One mean value step on the segment `[-|x|, |x|]`. -/
theorem abs_sub_le_of_deriv_bound (φ ψ : ℝ → ℝ) (x B : ℝ)
    (hd : ∀ t, |t| ≤ |x| → HasDerivAt φ (ψ t) t)
    (hb : ∀ t, |t| ≤ |x| → |ψ t| ≤ B) :
    |φ x - φ 0| ≤ B * |x| := by
  have hconv : Convex ℝ (Set.Icc (-|x|) |x|) := convex_Icc _ _
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := ψ)
    (fun t ht => (hd t (abs_le.mpr ht)).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using hb t (abs_le.mpr ht))
    (⟨by simp, abs_nonneg x⟩ : (0 : ℝ) ∈ Set.Icc (-|x|) |x|)
    (⟨neg_abs_le x, le_abs_self x⟩ : x ∈ Set.Icc (-|x|) |x|)
  simpa [Real.norm_eq_abs] using h

/-- Derivative of a directional iterated derivative along a line. -/
theorem hasDerivAt_iteratedFDeriv_line (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 4 F U) {k : ℕ} (hk : k < 4) (p v : ℝ × ℝ) (m : Fin k → ℝ × ℝ)
    (t : ℝ) (ht : p + t • v ∈ U) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (p + τ • v) m)
      (iteratedFDeriv ℝ (k + 1) F (p + t • v) (Fin.cons v m)) t := by
  have hca : ContDiffAt ℝ 4 F (p + t • v) := hF.contDiffAt (hU.mem_nhds ht)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) (p + t • v) :=
    hca.differentiableAt_iteratedFDeriv (by exact_mod_cast hk)
  have hline : HasDerivAt (fun τ : ℝ => p + τ • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have h := (hdiff.hasFDerivAt.continuousMultilinear_apply_const m).comp_hasDerivAt t hline
  have hval : iteratedFDeriv ℝ (k + 1) F (p + t • v) (Fin.cons v m) =
      ((fderiv ℝ (iteratedFDeriv ℝ k F) (p + t • v)).flipMultilinear m) v := by
    rw [iteratedFDeriv_succ_apply_left]
    simp
  rw [hval]
  exact h

/-- Smoothness and jet hypotheses on the remainder `R(tau, z)` (uncurried as `F`):
`C⁴` on an open set `U` containing the box `|tau|, |z| ≤ r ≤ 1`, vanishing on the axis
`z = 0`, and with
`∂_z R = ∂_tau ∂_z R = ∂_z² R = ∂_tau ∂_z² R = ∂_z³ R = 0` at the origin. -/
structure PitchforkJet (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ 4 F U
  r_pos : 0 < r
  r_le_one : r ≤ 1
  box_sub : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U
  trivial : ∀ e, |e| ≤ r → F (e, 0) = 0
  jet_z : iteratedFDeriv ℝ 1 F 0 ![eZ] = 0
  jet_tau_z : iteratedFDeriv ℝ 2 F 0 ![eTau, eZ] = 0
  jet_zz : iteratedFDeriv ℝ 2 F 0 ![eZ, eZ] = 0
  jet_tau_zz : iteratedFDeriv ℝ 3 F 0 ![eTau, eZ, eZ] = 0
  jet_zzz : iteratedFDeriv ℝ 3 F 0 ![eZ, eZ, eZ] = 0

variable {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {r : ℝ}

theorem PitchforkJet.mem_U (h : PitchforkJet F U r) {e z : ℝ} (he : |e| ≤ r) (hs : |z| ≤ r) :
    ((e, z) : ℝ × ℝ) ∈ U :=
  h.box_sub ((mem_box r e z).2 ⟨he, hs⟩)

/-- Derivative in `z` of a directional iterated derivative at `(e, t)`. -/
theorem PitchforkJet.hasDerivAt_s (h : PitchforkJet F U r) {k : ℕ} (hk : k < 4) (m : Fin k → ℝ × ℝ)
    {e t : ℝ} (he : |e| ≤ r) (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (e, τ) m)
      (iteratedFDeriv ℝ (k + 1) F (e, t) (Fin.cons eZ m)) t := by
  have hp (τ : ℝ) : ((e, 0) : ℝ × ℝ) + τ • eZ = (e, τ) := by ext <;> simp [eZ]
  have := hasDerivAt_iteratedFDeriv_line F U h.isOpen h.smooth hk (e, 0) eZ m t
    (by rw [hp]; exact h.mem_U he ht)
  simp only [hp] at this
  exact this

/-- Derivative in the parameter of a directional iterated derivative at `(t, 0)`. -/
theorem PitchforkJet.hasDerivAt_tau (h : PitchforkJet F U r) {k : ℕ} (hk : k < 4) (m : Fin k → ℝ × ℝ)
    {t : ℝ} (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (τ, 0) m)
      (iteratedFDeriv ℝ (k + 1) F (t, 0) (Fin.cons eTau m)) t := by
  have hp (τ : ℝ) : (0 : ℝ × ℝ) + τ • eTau = (τ, 0) := by ext <;> simp [eTau]
  have := hasDerivAt_iteratedFDeriv_line F U h.isOpen h.smooth hk 0 eTau m t
    (by rw [hp]; exact h.mem_U ht (by simpa using h.r_pos.le))
  simp only [hp] at this
  exact this

/-- Uniform bounds on the third and fourth derivatives on the closed box. -/
theorem PitchforkJet.exists_bound (h : PitchforkJet F U r) : ∃ M, 0 ≤ M ∧
    (∀ e z, |e| ≤ r → |z| ≤ r → ∀ m : Fin 3 → ℝ × ℝ,
      |iteratedFDeriv ℝ 3 F (e, z) m| ≤ M * ∏ i, ‖m i‖) ∧
    (∀ e z, |e| ≤ r → |z| ≤ r → ∀ m : Fin 4 → ℝ × ℝ,
      |iteratedFDeriv ℝ 4 F (e, z) m| ≤ M * ∏ i, ‖m i‖) := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) r) := isCompact_closedBall _ _
  have hc (k : ℕ) (hk : k ≤ 4) :
      ContinuousOn (iteratedFDeriv ℝ k F) (Metric.closedBall (0 : ℝ × ℝ) r) := fun q hq =>
    ((h.smooth.contDiffAt (h.isOpen.mem_nhds (h.box_sub hq))).continuousAt_iteratedFDeriv
      (by exact_mod_cast hk)).continuousWithinAt
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn (hc 3 (by norm_num))
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn (hc 4 le_rfl)
  refine ⟨max (max M3 M4) 0, le_max_right _ _, ?_, ?_⟩
  · intro e z he hs m
    have hq := hM3 _ ((mem_box r e z).2 ⟨he, hs⟩)
    have hle := (iteratedFDeriv ℝ 3 F (e, z)).le_opNorm m
    rw [Real.norm_eq_abs] at hle
    have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    calc _ ≤ _ := hle
      _ ≤ max (max M3 M4) 0 * ∏ i, ‖m i‖ :=
        mul_le_mul_of_nonneg_right (hq.trans ((le_max_left _ _).trans (le_max_left _ _))) hp
  · intro e z he hs m
    have hq := hM4 _ ((mem_box r e z).2 ⟨he, hs⟩)
    have hle := (iteratedFDeriv ℝ 4 F (e, z)).le_opNorm m
    rw [Real.norm_eq_abs] at hle
    have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    calc _ ≤ _ := hle
      _ ≤ max (max M3 M4) 0 * ∏ i, ‖m i‖ :=
        mul_le_mul_of_nonneg_right (hq.trans ((le_max_right _ _).trans (le_max_left _ _))) hp

/-! ## Bounds from the jets -/

/-- A bound `M` for the third and fourth derivatives on the box. -/
def DerivBound (F : ℝ × ℝ → ℝ) (r M : ℝ) : Prop :=
  0 ≤ M ∧ (∀ e z, |e| ≤ r → |z| ≤ r → ∀ m : Fin 3 → ℝ × ℝ,
      |iteratedFDeriv ℝ 3 F (e, z) m| ≤ M * ∏ i, ‖m i‖) ∧
    (∀ e z, |e| ≤ r → |z| ≤ r → ∀ m : Fin 4 → ℝ × ℝ,
      |iteratedFDeriv ℝ 4 F (e, z) m| ≤ M * ∏ i, ‖m i‖)

variable {M : ℝ}

theorem DerivBound.b3 (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r) (hs : |z| ≤ r)
    (m : Fin 3 → ℝ × ℝ) (hm : ∏ i, ‖m i‖ = 1) : |iteratedFDeriv ℝ 3 F (e, z) m| ≤ M := by
  simpa [hm] using hB.2.1 e z he hs m

theorem DerivBound.b4 (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r) (hs : |z| ≤ r)
    (m : Fin 4 → ℝ × ℝ) (hm : ∏ i, ‖m i‖ = 1) : |iteratedFDeriv ℝ 4 F (e, z) m| ≤ M := by
  simpa [hm] using hB.2.2 e z he hs m

theorem PitchforkJet.zero_le_r (h : PitchforkJet F U r) : |(0 : ℝ)| ≤ r := by simpa using h.r_pos.le

/-- `|∂_z³ R(tau, 0)| ≤ M |tau|`. -/
theorem zzz_axis (h : PitchforkJet F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, 0) ![eZ, eZ, eZ]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eZ, eZ, eZ])
    (fun τ => iteratedFDeriv ℝ 4 F (τ, 0) ![eTau, eZ, eZ, eZ]) e M
    (fun t ht => h.hasDerivAt_tau (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b4 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eZ, norm_eTau]))
  simp only [Prod.mk_zero_zero, h.jet_zzz, sub_zero] at key
  exact key

/-- `|∂_z³ R(tau, z)| ≤ M (|tau| + |z|)`. -/
theorem sss_bound (h : PitchforkJet F U r) (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, z) ![eZ, eZ, eZ]| ≤ M * (|e| + |z|) := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (e, τ) ![eZ, eZ, eZ])
    (fun τ => iteratedFDeriv ℝ 4 F (e, τ) ![eZ, eZ, eZ, eZ]) z M
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => hB.b4 he (ht.trans hs) _
      (by simp [Fin.prod_univ_succ, norm_eZ]))
  have h0 := zzz_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 3 F (e, z) ![eZ, eZ, eZ])
    (iteratedFDeriv ℝ 3 F (e, 0) ![eZ, eZ, eZ])
  linarith

/-- `|∂_tau ∂_z² R(tau, 0)| ≤ M |tau|`. -/
theorem tauzz_axis (h : PitchforkJet F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, 0) ![eTau, eZ, eZ]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eTau, eZ, eZ])
    (fun τ => iteratedFDeriv ℝ 4 F (τ, 0) ![eTau, eTau, eZ, eZ]) e M
    (fun t ht => h.hasDerivAt_tau (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b4 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eZ, norm_eTau]))
  simp only [Prod.mk_zero_zero, h.jet_tau_zz, sub_zero] at key
  exact key

/-- `|∂_z² R(tau, 0)| ≤ M tau ^ 2`. -/
theorem zz_axis (h : PitchforkJet F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, 0) ![eZ, eZ]| ≤ M * e ^ 2 := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eZ, eZ])
    (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eTau, eZ, eZ]) e (M * |e|)
    (fun t ht => h.hasDerivAt_tau (by norm_num) _ (ht.trans he))
    (fun t ht => (tauzz_axis h hB (ht.trans he)).trans (mul_le_mul_of_nonneg_left ht hM))
  simp only [Prod.mk_zero_zero, h.jet_zz, sub_zero] at key
  rw [← sq_abs e]
  linarith [key]

/-- `|∂_z² R(tau, z)| ≤ M (tau ^ 2 + |z| (|tau| + |z|))`. -/
theorem ss_bound (h : PitchforkJet F U r) (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, z) ![eZ, eZ]| ≤ M * (e ^ 2 + |z| * (|e| + |z|)) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eZ, eZ])
    (fun τ => iteratedFDeriv ℝ 3 F (e, τ) ![eZ, eZ, eZ]) z (M * (|e| + |z|))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (sss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hM))
  have h0 := zz_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 2 F (e, z) ![eZ, eZ])
    (iteratedFDeriv ℝ 2 F (e, 0) ![eZ, eZ])
  nlinarith

/-- `|∂_tau ∂_z R(tau, 0)| ≤ M |tau|`. -/
theorem tauz_axis (h : PitchforkJet F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, 0) ![eTau, eZ]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eTau, eZ])
    (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eTau, eTau, eZ]) e M
    (fun t ht => h.hasDerivAt_tau (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b3 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eZ, norm_eTau]))
  simp only [Prod.mk_zero_zero, h.jet_tau_z, sub_zero] at key
  exact key

/-- `|∂_z R(tau, 0)| ≤ M tau ^ 2`. -/
theorem z_axis (h : PitchforkJet F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, 0) ![eZ]| ≤ M * e ^ 2 := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (τ, 0) ![eZ])
    (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eTau, eZ]) e (M * |e|)
    (fun t ht => h.hasDerivAt_tau (by norm_num) _ (ht.trans he))
    (fun t ht => (tauz_axis h hB (ht.trans he)).trans (mul_le_mul_of_nonneg_left ht hM))
  simp only [Prod.mk_zero_zero, h.jet_z, sub_zero] at key
  rw [← sq_abs e]
  linarith [key]

/-- The derivative bound `|∂_z R(tau, z)| ≤ 2M (tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)` (`|z| ≤ 1`). -/
theorem s_bound (h : PitchforkJet F U r) (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, z) ![eZ]| ≤ 2 * M * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eZ])
    (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eZ, eZ]) z (M * (e ^ 2 + |z| * (|e| + |z|)))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (ss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have := mul_le_mul ht (add_le_add_left ht |e|) (by positivity) (abs_nonneg z)
        linarith) hM))
  have h0 := z_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 1 F (e, z) ![eZ])
    (iteratedFDeriv ℝ 1 F (e, 0) ![eZ])
  have hs1 : |z| ≤ 1 := hs.trans h.r_le_one
  have hes : e ^ 2 * |z| ≤ e ^ 2 := by nlinarith [sq_nonneg e, abs_nonneg z]
  have hid : M * (e ^ 2 + |z| * (|e| + |z|)) * |z| =
      M * (e ^ 2 * |z| + z ^ 2 * |e| + |z| ^ 3) := by rw [← sq_abs z]; ring
  have hle : M * (e ^ 2 * |z| + z ^ 2 * |e| + |z| ^ 3) ≤ M * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  have he2 : M * e ^ 2 ≤ M * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) :=
    mul_le_mul_of_nonneg_left (by
      have : 0 ≤ z ^ 2 * |e| + |z| ^ 3 := by positivity
      linarith) hM
  linarith

/-- `R(tau, ·)` has derivative `∂_z R(tau, t)` at `t`. -/
theorem hasDerivAt_F (h : PitchforkJet F U r) {e t : ℝ} (he : |e| ≤ r) (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => F (e, τ)) (iteratedFDeriv ℝ 1 F (e, t) ![eZ]) t :=
  h.hasDerivAt_s (k := 0) (by norm_num) (![] : Fin 0 → ℝ × ℝ) he ht

/-- The weak value bound `|R(tau, z)| ≤ 2M (|z| tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)`. -/
theorem value_bound (h : PitchforkJet F U r) (hB : DerivBound F r M) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |F (e, z)| ≤ 2 * M * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => F (e, τ))
    (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eZ]) z (2 * M * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (fun t ht => hasDerivAt_F h he (ht.trans hs))
    (fun t ht => (s_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have h2 : t ^ 2 ≤ z ^ 2 := by rw [← sq_abs t, ← sq_abs z]; gcongr
        have h3 : |t| ^ 3 ≤ |z| ^ 3 := by gcongr
        have := mul_le_mul_of_nonneg_right h2 (abs_nonneg e)
        linarith) (by positivity)))
  simp only [h.trivial e he, sub_zero] at key
  calc |F (e, z)| ≤ 2 * M * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3) * |z| := key
    _ = 2 * M * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
      rw [← (by decide : Even 4).pow_abs z, ← sq_abs z]; ring

/-- Under the axis condition `∂_z R(tau, 0) = 0`, the stronger derivative bound
`|∂_z R(tau, z)| ≤ M (|z| tau ^ 2 + z ^ 2 |tau| + |z| ^ 3)`. -/
theorem s_bound_strong (h : PitchforkJet F U r) (hB : DerivBound F r M)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 F (e, 0) ![eZ] = 0) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, z) ![eZ]| ≤ M * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eZ])
    (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eZ, eZ]) z (M * (e ^ 2 + |z| * (|e| + |z|)))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (ss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have := mul_le_mul ht (add_le_add_left ht |e|) (by positivity) (abs_nonneg z)
        linarith) hM))
  simp only [hlin e he, sub_zero] at key
  calc _ ≤ M * (e ^ 2 + |z| * (|e| + |z|)) * |z| := key
    _ = M * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3) := by rw [← sq_abs z]; ring

/-- Under the axis condition `∂_z R(tau, 0) = 0`, the stronger value bound
`|R(tau, z)| ≤ M (z ^ 2 tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)`. -/
theorem value_bound_strong (h : PitchforkJet F U r) (hB : DerivBound F r M)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 F (e, 0) ![eZ] = 0) {e z : ℝ} (he : |e| ≤ r)
    (hs : |z| ≤ r) :
    |F (e, z)| ≤ M * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => F (e, τ))
    (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eZ]) z (M * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (fun t ht => hasDerivAt_F h he (ht.trans hs))
    (fun t ht => (s_bound_strong h hB hlin he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have h1 := mul_le_mul_of_nonneg_right ht (sq_nonneg e)
        have h2 : t ^ 2 ≤ z ^ 2 := by rw [← sq_abs t, ← sq_abs z]; gcongr
        have h3 : |t| ^ 3 ≤ |z| ^ 3 := by gcongr
        have := mul_le_mul_of_nonneg_right h2 (abs_nonneg e)
        linarith) hM))
  simp only [h.trivial e he, sub_zero] at key
  calc |F (e, z)| ≤ M * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3) * |z| := key
    _ = M * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
      rw [← (by decide : Even 4).pow_abs z, ← sq_abs z]; ring

/-! ## The remainder bounds from smoothness and jets -/

/-- The `z`-derivative `∂_z R(tau, z)` of a two-variable remainder, as a directional
iterated Fréchet derivative. -/
noncomputable def jetRs (R : ℝ → ℝ → ℝ) (e z : ℝ) : ℝ :=
  iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![eZ]

/-- **The remainder bounds follow from smoothness and jets.** If the remainder
`R(tau, z)` is `C⁴` on an open set containing the box `|tau|, |z| ≤ r ≤ 1`, vanishes on the
axis `z = 0`, and satisfies the five jet conditions
`∂_z R = ∂_tau ∂_z R = ∂_z² R = ∂_tau ∂_z² R = ∂_z³ R = 0` at the origin, then there is
`C ≥ 0` with the weak value bound, the `z`-derivative `jetRs R`, the matching derivative
bound, and continuity of `tau ↦ R(tau, z)`: exactly the hypotheses of
`exists_branch_eventually` and `pitchfork_branch_curves`. -/
theorem remainderBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : PitchforkJet (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (jetRs R e z) z) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |jetRs R e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) ∧
      (∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) := by
  obtain ⟨M, hM, h3, h4⟩ := h.exists_bound
  have hB : DerivBound (Function.uncurry R) r M := ⟨hM, h3, h4⟩
  refine ⟨2 * M, by positivity, fun e z he hs => value_bound h hB he hs,
    fun e z he hs => hasDerivAt_F h he hs, fun e z he hs => s_bound h hB he hs, ?_⟩
  intro e z he hs
  have hF : ContinuousAt (Function.uncurry R) (e, z) :=
    h.smooth.continuousOn.continuousAt (h.isOpen.mem_nhds (h.mem_U he.le hs))
  exact hF.comp (f := fun e' : ℝ => ((e', z) : ℝ × ℝ)) (by fun_prop)

/-- Both stronger bounds follow when in addition the axis condition
`∂_z R(tau, 0) = 0` holds on the box. -/
theorem strongBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : PitchforkJet (Function.uncurry R) U r)
    (hlin : ∀ e, |e| ≤ r → jetRs R e 0 = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        |jetRs R e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) := by
  obtain ⟨M, hM, h3, h4⟩ := h.exists_bound
  have hB : DerivBound (Function.uncurry R) r M := ⟨hM, h3, h4⟩
  exact ⟨M, hM, fun e z he hs => value_bound_strong h hB hlin he hs,
    fun e z he hs => s_bound_strong h hB hlin he hs⟩

/-- A differentiable `φ` with `|φ z| ≤ K z ^ 2` near `0` has derivative `0` at `0`;
this is the converse direction of `strongBound_iff_axis`. -/
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ z, |z| ≤ δ → |φ z| ≤ K * z ^ 2) : d = 0 := by
  have h0 : φ 0 = 0 := by simpa using hb 0 (by simpa using hδ.le)
  have hK : HasDerivAt φ 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, h0, sub_zero, smul_zero]
    have hsq : (fun z : ℝ => z ^ 2) =o[𝓝 0] fun z => z := by
      have := (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
      simpa using this
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hsq
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with z hs
    have := hb z (by simpa [Real.dist_eq] using hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)] using this
  exact hd.unique hK

/-- Under the jet hypotheses, the stronger value bound holds on the box if and only
if the axis condition `∂_z R(tau, 0) = 0` holds on the box. -/
theorem strongBound_iff_axis (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : PitchforkJet (Function.uncurry R) U r) :
    (∃ C, ∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ↔
      ∀ e, |e| ≤ r → jetRs R e 0 = 0 := by
  constructor
  · rintro ⟨C, hC⟩ e he
    refine deriv_zero_of_sq_bound (R e) _ (C * (r ^ 2 + r + 1)) r h.r_pos
      (hasDerivAt_F h he h.zero_le_r) fun z hs => ?_
    have h1 := hC e z he hs
    have hr1 := h.r_le_one
    have hs1 : |z| ≤ 1 := hs.trans hr1
    have hC0 : 0 ≤ C := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      have := hC e r he (by rw [abs_of_pos h.r_pos])
      have hpos : 0 < r ^ 2 * e ^ 2 + |r| ^ 3 * |e| + r ^ 4 := by
        have : 0 < r ^ 4 := by have := h.r_pos; positivity
        positivity
      nlinarith [abs_nonneg (R e r)]
    have he2 : e ^ 2 ≤ r ^ 2 := by rw [← sq_abs e]; gcongr
    have hs3 : |z| ^ 3 * |e| ≤ z ^ 2 * r := by
      have : |z| ^ 3 ≤ z ^ 2 := by
        rw [← sq_abs z]; nlinarith [abs_nonneg z, sq_nonneg |z|]
      nlinarith [abs_nonneg e, pow_nonneg (abs_nonneg z) 3, sq_nonneg z]
    have hs4 : z ^ 4 ≤ z ^ 2 := by
      have : z ^ 2 ≤ 1 := by rw [← sq_abs z]; nlinarith [abs_nonneg z]
      nlinarith [sq_nonneg z]
    calc |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := h1
      _ ≤ C * (z ^ 2 * r ^ 2 + z ^ 2 * r + z ^ 2) := by
        have := mul_le_mul_of_nonneg_left he2 (sq_nonneg z)
        exact mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = C * (r ^ 2 + r + 1) * z ^ 2 := by ring
  · intro hlin
    obtain ⟨C, -, hv, -⟩ := strongBounds_of_jet R U r h hlin
    exact ⟨C, hv⟩

/-- Non-vacuity: the zero remainder satisfies all smoothness and jet hypotheses
(on `U = univ`, any `0 < r ≤ 1`). -/
theorem pitchforkJet_zero (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    PitchforkJet (Function.uncurry fun _ _ : ℝ => (0 : ℝ)) Set.univ r := by
  have hz : Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ => 0 := rfl
  refine ⟨isOpen_univ, contDiffOn_const, hr, hr1, Set.subset_univ _, fun _ _ => rfl, ?_, ?_,
    ?_, ?_, ?_⟩ <;> simp [hz]

/-! ## Corollaries: the branch theorems from smoothness and jets -/

/-- `exists_branch_eventually` with the remainder bounds discharged by
`remainderBounds_of_jet`: from `C⁴` smoothness and the jet conditions alone, for all small
`tau` on the side `tau * beta > 0` there are zeros of both signs with amplitude
`√(alpha tau / beta) + O(|tau|)` and `(∂_z field) * beta < 0`. -/
theorem exists_branch_eventually_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (h : PitchforkJet (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        pitchforkField alpha beta R tau z = 0 ∧
        abs (|z| - Real.sqrt (alpha * tau / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (pitchforkField alpha beta R tau) z * beta < 0 := by
  obtain ⟨C, hC, hv, hd, hs, -⟩ := remainderBounds_of_jet R U r h
  exact ⟨C, hC, exists_branch_eventually alpha beta C r R (jetRs R) halpha hbeta hC h.r_pos
    h.r_le_one hv hd hs⟩

/-- `pitchfork_branch_curves` from `C⁴` smoothness and the jet conditions alone:
the continuous branch curves, their local uniqueness, amplitude and derivative sign, with
no derivative bound taken as input. -/
theorem pitchfork_branch_curves_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (h : PitchforkJet (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧
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
  obtain ⟨C, hC, hv, hd, hs, hc⟩ := remainderBounds_of_jet R U r h
  exact ⟨C, hC, pitchfork_branch_curves alpha beta C r R (jetRs R) halpha hbeta hC h.r_pos h.r_le_one
    hv hd hs hc⟩

end ScalarPitchfork
