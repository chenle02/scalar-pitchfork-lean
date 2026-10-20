/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarPitchfork.Jet

/-!
# The jets do not give the stronger remainder bound

The remainder `R(tau, z) = tau ^ 2 * z` is polynomial, vanishes on the axis `z = 0`, and
all five jets of `PitchforkJet` vanish at the origin, but `∂_z R(tau, 0) = tau ^ 2 ≠ 0`.
By `strongBound_iff_axis`, no stronger bound
`|R(tau, z)| ≤ C (z ^ 2 tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)` holds on any box
(`cex_not_strongBound`, `jet_not_sufficient_for_strongBound`).

The axis condition does hold when the linear part of the field along the axis is exactly
`alpha * tau * z`: if `f(tau, z) = alpha tau z - beta z ^ 3 + R(tau, z)` and
`∂_z f(tau, 0) = alpha * tau` for `|tau| ≤ r`, then `∂_z R(tau, 0) = 0` on the box
(`axis_of_linearization`).
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork

open Filter Topology

/-! ## Iterated derivatives along lines -/

/-- Line-derivative characterization of a directional iterated derivative:
`D^{k+1}F(p)[v, m] = d/dτ D^kF(p + τ v)[m]` at `τ = 0`. -/
theorem iteratedFDeriv_succ_eq_of_line (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 4 F) {k : ℕ}
    (hk : k < 4) (p v : ℝ × ℝ) (m : Fin k → ℝ × ℝ) (d : ℝ)
    (hd : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (p + τ • v) m) d 0) :
    iteratedFDeriv ℝ (k + 1) F p (Fin.cons v m) = d := by
  have h := hasDerivAt_iteratedFDeriv_line F Set.univ isOpen_univ hF.contDiffOn hk p v m 0
    (Set.mem_univ _)
  rw [zero_smul, add_zero] at h
  exact h.unique hd

/-! ## The counterexample `tau ^ 2 * z` -/

/-- The counterexample remainder `R(tau, z) = tau ^ 2 * z`. -/
def cexR (e z : ℝ) : ℝ := e ^ 2 * z

theorem uncurry_cexR : Function.uncurry cexR = fun q : ℝ × ℝ => q.1 ^ 2 * q.2 := by
  funext q
  rfl

theorem contDiff_cexR : ContDiff ℝ 4 (Function.uncurry cexR) := by
  rw [uncurry_cexR]
  exact (contDiff_fst.pow 2).mul contDiff_snd

/-- `∂_z R(tau, z) = tau ^ 2` for `R = tau ^ 2 * z`. -/
theorem cex_d_s (e z : ℝ) :
    iteratedFDeriv ℝ 1 (Function.uncurry cexR) (e, z) ![eZ] = e ^ 2 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 0) (by norm_num) (e, z) eZ ![]
    (e ^ 2) ?_
  have hfun : (fun τ : ℝ => iteratedFDeriv ℝ 0 (Function.uncurry cexR) ((e, z) + τ • eZ) ![]) =
      fun τ => e ^ 2 * (z + τ) := by
    funext τ
    simp [eZ, cexR]
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_add z).const_mul (e ^ 2)

/-- `∂_tau ∂_z R(tau, z) = 2 tau` for `R = tau ^ 2 * z`. -/
theorem cex_d_eta_s (e z : ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry cexR) (e, z) ![eTau, eZ] = 2 * e := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 1) (by norm_num) (e, z) eTau
    ![eZ] (2 * e) ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 1 (Function.uncurry cexR) ((e, z) + τ • eTau) ![eZ]) =
      fun τ => (e + τ) ^ 2 := by
    funext τ
    have hp : ((e, z) : ℝ × ℝ) + τ • eTau = (e + τ, z) := by ext <;> simp [eTau]
    rw [hp, cex_d_s]
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_add e).fun_pow 2

/-- `∂_z² R(tau, z) = 0` for `R = tau ^ 2 * z`. -/
theorem cex_d_ss (e z : ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry cexR) (e, z) ![eZ, eZ] = 0 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 1) (by norm_num) (e, z) eZ
    ![eZ] 0 ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 1 (Function.uncurry cexR) ((e, z) + τ • eZ) ![eZ]) =
      fun _ => e ^ 2 := by
    funext τ
    have hp : ((e, z) : ℝ × ℝ) + τ • eZ = (e, z + τ) := by ext <;> simp [eZ]
    rw [hp, cex_d_s]
  rw [hfun]
  exact hasDerivAt_const _ _

/-- `∂_v ∂_z² R(tau, z) = 0` for `R = tau ^ 2 * z` and any direction `v`. -/
theorem cex_d3 (v : ℝ × ℝ) (e z : ℝ) :
    iteratedFDeriv ℝ 3 (Function.uncurry cexR) (e, z) ![v, eZ, eZ] = 0 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 2) (by norm_num) (e, z) v
    ![eZ, eZ] 0 ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 2 (Function.uncurry cexR) ((e, z) + τ • v) ![eZ, eZ]) =
      fun _ => 0 := by
    funext τ
    have hp : ((e, z) : ℝ × ℝ) + τ • v = (e + τ * v.1, z + τ * v.2) := by ext <;> simp
    rw [hp, cex_d_ss]
  rw [hfun]
  exact hasDerivAt_const _ _

/-- The counterexample satisfies all smoothness and jet hypotheses of
`PitchforkJet` (on `U = univ`, any `0 < r ≤ 1`). -/
theorem pitchforkJet_cex (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    PitchforkJet (Function.uncurry cexR) Set.univ r := by
  have h0 : (0 : ℝ × ℝ) = ((0 : ℝ), (0 : ℝ)) := rfl
  refine ⟨isOpen_univ, contDiff_cexR.contDiffOn, hr, hr1, Set.subset_univ _,
    fun e _ => by simp [cexR], ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, cex_d_s]; ring
  · rw [h0, cex_d_eta_s]; ring
  · rw [h0, cex_d_ss]
  · rw [h0, cex_d3]
  · rw [h0, cex_d3]

/-- The `z`-derivative of the counterexample: `∂_z R(tau, z) = tau ^ 2`. -/
theorem jetRs_cex (e z : ℝ) : jetRs cexR e z = e ^ 2 := cex_d_s e z

/-- **The counterexample violates the stronger bound on every box.** For
`R(tau, z) = tau ^ 2 * z` and any `r > 0` there is no `C` with
`|R(tau, z)| ≤ C (z ^ 2 tau ^ 2 + |z| ^ 3 |tau| + z ^ 4)` for `|tau|, |z| ≤ r`. -/
theorem cex_not_strongBound (r : ℝ) (hr : 0 < r) :
    ¬ ∃ C, ∀ e z, |e| ≤ r → |z| ≤ r →
      |cexR e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := by
  rintro ⟨C, hC⟩
  set r' := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr one_pos
  have hiff := strongBound_iff_axis cexR Set.univ r' (pitchforkJet_cex r' hr'0 (min_le_right _ _))
  have hax := hiff.1 ⟨C, fun e z he hs => hC e z (he.trans (min_le_left _ _))
    (hs.trans (min_le_left _ _))⟩ r' (by rw [abs_of_pos hr'0])
  rw [jetRs_cex] at hax
  exact hr'0.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hax)

/-- **The jets alone do not give the stronger bound.** It is false that every
remainder satisfying `PitchforkJet` admits the stronger value bound; the axis condition of
`strongBound_iff_axis` is genuinely needed. -/
theorem jet_not_sufficient_for_strongBound :
    ¬ ∀ (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ), PitchforkJet (Function.uncurry R) U r →
      ∃ C, ∀ e z, |e| ≤ r → |z| ≤ r →
        |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4) := fun hall =>
  cex_not_strongBound 1 one_pos (hall cexR Set.univ 1 (pitchforkJet_cex 1 one_pos le_rfl))

/-! ## The axis condition from the linearization along the axis -/

/-- The remainder of a field `f` after the cubic normal form:
`R(tau, z) = f(tau, z) - alpha tau z + beta z ^ 3`. -/
noncomputable def remainderOf (alpha beta : ℝ) (f : ℝ → ℝ → ℝ) (e z : ℝ) : ℝ :=
  f e z - alpha * e * z + beta * z ^ 3

/-- The linear part of the field `f` along the axis `z = 0` is exactly
`alpha * tau`: `∂_z f(tau, 0) = alpha * tau` for `|tau| ≤ r`. -/
def AxisLinearization (alpha : ℝ) (f : ℝ → ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ e, |e| ≤ r → HasDerivAt (f e) (alpha * e) 0

/-- **The axis condition from the linearization along the axis.** If the remainder
of `f` satisfies `PitchforkJet` and `∂_z f(tau, 0) = alpha * tau` on the box, then
`∂_z R(tau, 0) = 0` on the box; by `strongBounds_of_jet` the stronger bounds follow. -/
theorem axis_of_linearization (alpha beta : ℝ) (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : PitchforkJet (Function.uncurry (remainderOf alpha beta f)) U r)
    (hlin : AxisLinearization alpha f r) :
    ∀ e, |e| ≤ r → jetRs (remainderOf alpha beta f) e 0 = 0 := by
  intro e he
  have h1 := hasDerivAt_F h he h.zero_le_r
  have h2 := ((hlin e he).sub ((hasDerivAt_id (0 : ℝ)).const_mul (alpha * e))).add
    ((hasDerivAt_pow 3 (0 : ℝ)).const_mul beta)
  have h3 : jetRs (remainderOf alpha beta f) e 0 = _ := h1.unique h2
  rw [h3]
  simp

end ScalarPitchfork
