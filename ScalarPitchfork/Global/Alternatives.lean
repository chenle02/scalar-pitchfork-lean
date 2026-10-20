/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Connected.Clopen
public import ScalarPitchfork.Global.ComponentClosure

/-!
# Global bifurcation alternatives: the topological skeleton

The unilateral global bifurcation theorem (Rabinowitz; in the unilateral form of
Shi–Wang) asserts that a unilateral component `C ⊆ ℝ × E` of nontrivial
solutions emanating from a bifurcation point `(λ*, u*)` satisfies one of three
alternatives:

1. `C` is not compact;
2. `C` meets the trivial branch `{(λ, u*)}` at another parameter `λ ≠ λ*`;
3. `C` contains a point `(λ, u* + w)` with `w ≠ 0` in a complement `W` of the
   kernel direction.

This file formalizes the logical deductions that turn these alternatives into
global conclusions, with all analytic inputs kept as explicit hypotheses:

* elimination of alternatives: if (2) and (3) fail, `C` is not compact;
* relative closedness in an admissible set `V` plus admissibility of limits
  (`closure S ⊆ V`) gives closedness in the ambient space;
* precompactness of bounded-parameter pieces of the solution set `S` makes
  bounded-parameter slices of `C` compact, so a non-compact `C` has unbounded
  parameter, `sup {λ : (λ, u) ∈ C} = +∞` in `EReal` (`sSup_param_eq_top`);
* connectedness propagation: a property whose locus is relatively clopen in a
  preconnected component and holds at the bifurcation point holds on all of it;
* for branches of strictly monotone profiles on `[0, L]`, alternatives (2) and
  (3) are excluded, the latter through any weight `φ` that pairs positively with
  every continuous strictly decreasing profile and is orthogonal to `W`
  (`global_unbounded_of_monotone`).
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork.Global

open Set Filter Topology MeasureTheory intervalIntegral

section Alternatives

variable {E : Type*}

/-- Alternative (1): the component is not compact. -/
def AltNoncompact [TopologicalSpace E] (C : Set (ℝ × E)) : Prop :=
  ¬ IsCompact C

/-- Alternative (2): the component meets the trivial branch `{(λ, u*)}` at a
parameter different from the bifurcation value. -/
def AltOtherTrivial (C : Set (ℝ × E)) (lamStar : ℝ) (uStar : E) : Prop :=
  ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C

/-- Alternative (3): the component contains a point `(λ, u* + w)` with
`w ∈ W \ {0}`. -/
def AltComplement [Add E] [Zero E] (C : Set (ℝ × E)) (uStar : E) (W : Set E) :
    Prop :=
  ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C

/-- The disjunction delivered by the unilateral global bifurcation theorem
(Rabinowitz, Shi–Wang) for a unilateral component. -/
def GlobalAlternatives [TopologicalSpace E] [Add E] [Zero E] (C : Set (ℝ × E))
    (lamStar : ℝ) (uStar : E) (W : Set E) : Prop :=
  AltNoncompact C ∨ AltOtherTrivial C lamStar uStar ∨ AltComplement C uStar W

/-- **Alternative elimination**: if alternatives (2) and (3) fail, the component
is not compact. -/
theorem not_isCompact_of_alternatives [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {lamStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : GlobalAlternatives C lamStar uStar W)
    (hNotII : ¬ AltOtherTrivial C lamStar uStar)
    (hNotIII : ¬ AltComplement C uStar W) :
    ¬ IsCompact C := by
  rcases hAlt with h | h | h
  · exact h
  · exact absurd h hNotII
  · exact absurd h hNotIII

end Alternatives

section Compactness

variable {E : Type*} [TopologicalSpace E]

/-- A set relatively closed in `V` is closed in the ambient space once its
ambient closure stays inside `V`. -/
theorem isClosed_of_relClosed {C V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hClosureV : closure C ⊆ V) :
    IsClosed C := by
  obtain ⟨t, ht, hEq⟩ := isClosed_induced_iff.mp hRelClosed
  have hCt : C ⊆ t := by
    intro p hp
    have : (⟨p, hCV hp⟩ : V) ∈ ((↑) : V → ℝ × E) ⁻¹' t := by
      rw [hEq]; exact hp
    exact this
  refine closure_subset_iff_isClosed.mp ?_
  intro p hp
  have hpt : p ∈ t := closure_minimal hCt ht hp
  have : (⟨p, hClosureV hp⟩ : V) ∈ ((↑) : V → ℝ × E) ⁻¹' C := by
    rw [← hEq]; exact hpt
  exact this

/-- **Bounded-parameter slices are compact.**  If a closed set `C` lies in the
closure of a solution set `S` whose bounded-parameter pieces are relatively
compact (the usual a priori bounds plus a compact embedding), then each slice
`C ∩ {λ ≤ X}` is compact. -/
theorem isCompact_slice {C S : Set (ℝ × E)} (hClosed : IsClosed C)
    (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar}) := by
  have hSliceClosed : IsClosed (C ∩ {p : ℝ × E | p.1 ≤ Xbar}) :=
    hClosed.inter (isClosed_le continuous_fst continuous_const)
  refine (hPrecompact (Xbar + 1)).of_isClosed_subset hSliceClosed ?_
  have hOpen : IsOpen {p : ℝ × E | p.1 < Xbar + 1} :=
    isOpen_lt continuous_fst continuous_const
  intro p ⟨hpC, hpX⟩
  have hp : p ∈ {p : ℝ × E | p.1 < Xbar + 1} ∩ closure S :=
    ⟨show p.1 < Xbar + 1 by have : p.1 ≤ Xbar := hpX; linarith, hCS hpC⟩
  have := hOpen.inter_closure hp
  refine closure_mono ?_ this
  rintro q ⟨hq1, hq2⟩
  exact ⟨hq2, show q.1 ≤ Xbar + 1 from le_of_lt hq1⟩

/-- **Unbounded parameter from non-compactness**: if every bounded-parameter
slice is compact, a non-compact set has unbounded parameter. -/
theorem unbounded_of_not_isCompact {C : Set (ℝ × E)}
    (hSlice : ∀ Xbar : ℝ, IsCompact (C ∩ {p | p.1 ≤ Xbar}))
    (hNC : ¬ IsCompact C) :
    ∀ M : ℝ, ∃ p ∈ C, M < p.1 := by
  intro M
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  apply hNC
  have hEq : C ∩ {p | p.1 ≤ M} = C := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, hcon p h⟩⟩
  simpa [hEq] using hSlice M

omit [TopologicalSpace E] in
/-- Unbounded parameter written as `sup {λ : (λ, u) ∈ C} = +∞`, with the
supremum taken in the extended reals. -/
theorem sSup_eq_top_of_unbounded {C : Set (ℝ × E)}
    (hUnb : ∀ M : ℝ, ∃ p ∈ C, M < p.1) :
    sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot =>
    obtain ⟨p, hp, -⟩ := hUnb 0
    exact ⟨(p.1 : EReal), ⟨p, hp, rfl⟩, EReal.bot_lt_coe _⟩
  | coe x =>
    obtain ⟨p, hp, hlt⟩ := hUnb x
    exact ⟨(p.1 : EReal), ⟨p, hp, rfl⟩, EReal.coe_lt_coe_iff.mpr hlt⟩
  | top => exact absurd hb (lt_irrefl _)

/-- **A non-compact component has unbounded parameter.**  Hypotheses:
* `hRelClosed`, `hCV`: the component is relatively closed in the admissible
  set `V`;
* `hCS`: the component lies in the closure of the nontrivial-solution set `S`;
* `hAdmissible`: limits of solutions remain admissible, `closure S ⊆ V`;
* `hPrecompact`: bounded-parameter pieces of `S` are relatively compact.

Conclusion: a non-compact component has `sup λ = +∞`. -/
theorem sSup_param_eq_top {C S V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  have hClosed : IsClosed C :=
    isClosed_of_relClosed hRelClosed hCV
      ((closure_mono hCS).trans (closure_closure (s := S)).le |>.trans hAdmissible)
  have hUnb := unbounded_of_not_isCompact (isCompact_slice hClosed hCS hPrecompact) hNC
  exact ⟨hUnb, sSup_eq_top_of_unbounded hUnb⟩

/-- The unilateral component as a subset of `ℝ × E`: the `selectedComponent`
built in the admissible subtype `V` from the relative closure of the
nontrivial solutions `S`, included into `ℝ × E`. -/
def selectedImage (S V : Set (ℝ × E)) (removedArc : Set V) (base selector : V) :
    Set (ℝ × E) :=
  ((↑) : V → ℝ × E) ''
    selectedComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) removedArc base selector

/-- The unilateral component built inside the admissible subtype `V` is, after
inclusion into `ℝ × E`, relatively closed in `V`, contained in `V`, contained in
the ambient closure of `S`, and preconnected. -/
theorem selectedImage_properties {S V : Set (ℝ × E)}
    {removedArc : Set V} {base selector : V}
    (hBase : base ∈ closure (((↑) : V → ℝ × E) ⁻¹' S))
    (hRemovedRelOpen :
      IsOpen (((↑) : parentComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) base → V) ⁻¹'
        removedArc))
    (hSelectorInRemainder :
      selector ∈ unilateralRemainder (closure (((↑) : V → ℝ × E) ⁻¹' S)) removedArc base) :
    IsClosed (((↑) : V → ℝ × E) ⁻¹' selectedImage S V removedArc base selector) ∧
      selectedImage S V removedArc base selector ⊆ V ∧
      selectedImage S V removedArc base selector ⊆ closure S ∧
      IsPreconnected (selectedImage S V removedArc base selector) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [selectedImage, Subtype.val_injective.preimage_image]
    exact selectedComponent_isClosed isClosed_closure hBase hRemovedRelOpen
      hSelectorInRemainder
  · rintro _ ⟨q, -, rfl⟩
    exact q.property
  · rintro _ ⟨q, hq, rfl⟩
    have hq' := selectedComponent_subset_solutionClosure hq
    have := image_closure_subset_closure_image continuous_subtype_val ⟨q, hq', rfl⟩
    exact closure_mono (image_preimage_subset _ _) this
  · exact (isPreconnected_connectedComponentIn).image _ continuous_subtype_val.continuousOn

end Compactness

section Monotone

variable {E : Type*} [TopologicalSpace E]

/-- **Connectedness propagation**: a property holding at the bifurcation point
whose locus is relatively open and closed in a preconnected component holds on
the whole component. -/
theorem subset_of_relClopen {C M : Set (ℝ × E)} {pStar : ℝ × E}
    (hConn : IsPreconnected C) (hStar : pStar ∈ C) (hStarM : pStar ∈ M)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' M)) :
    C ⊆ M := by
  have := isPreconnected_iff_preconnectedSpace.mp hConn
  have hUniv := hClopen.eq_univ ⟨⟨pStar, hStar⟩, hStarM⟩
  intro p hp
  have : (⟨p, hp⟩ : C) ∈ ((↑) : C → ℝ × E) ⁻¹' M := by rw [hUniv]; trivial
  exact this

variable [AddCommGroup E]

/-- The points that are either the bifurcation point or have a strictly
decreasing profile on `[0, L]`. -/
def DecreasingLocus (prof : E →+ (ℝ → ℝ)) (L : ℝ) (pStar : ℝ × E) : Set (ℝ × E) :=
  {p | p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)}

/-- The points that are either the bifurcation point or have a strictly
increasing profile on `[0, L]`. -/
def IncreasingLocus (prof : E →+ (ℝ → ℝ)) (L : ℝ) (pStar : ℝ × E) : Set (ℝ × E) :=
  {p | p = pStar ∨ StrictMonoOn (prof p.2) (Icc 0 L)}

/-- **Strict decrease propagates along a component**: if the decreasing locus is
relatively clopen in a preconnected component through the bifurcation point,
every other point of the component has a strictly decreasing profile. -/
theorem strictAntiOn_of_relClopen (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' DecreasingLocus prof L pStar)) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) := by
  intro p hp hne
  rcases subset_of_relClopen hConn hStar (Or.inl rfl) hClopen hp with h | h
  · exact absurd h hne
  · exact h

/-- **Strict increase propagates along a component**: the increasing analogue of
`strictAntiOn_of_relClopen`. -/
theorem strictMonoOn_of_relClopen (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' IncreasingLocus prof L pStar)) :
    ∀ p ∈ C, p ≠ pStar → StrictMonoOn (prof p.2) (Icc 0 L) := by
  intro p hp hne
  rcases subset_of_relClopen hConn hStar (Or.inl rfl) hClopen hp with h | h
  · exact absurd h hne
  · exact h

omit [TopologicalSpace E] in
/-- **Alternative (2) fails for a strictly monotone branch**: the constant
profile `u*` is not strictly monotone. -/
theorem not_altOtherTrivial {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ AltOtherTrivial C lamStar uStar := by
  rintro ⟨lam, hne, hmem⟩
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have h1 : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  rcases hMono _ hmem (fun h => hne (Prod.ext_iff.mp h).1) with h | h
  · have := h h0 h1 hL; simp [hConst] at this
  · have := h h0 h1 hL; simp [hConst] at this

omit [TopologicalSpace E] in
/-- **Alternative (3) fails for a strictly monotone branch**: let `φ` be a weight
that pairs positively with every continuous strictly decreasing profile on
`[0, L]` (for instance the first Neumann cosine mode).  If every `w ∈ W` is
orthogonal to `φ`, then no profile `u* + w` with `w ∈ W \ {0}` is strictly
monotone.  The strictly increasing case follows by negation. -/
theorem not_altComplement {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hφ : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 L) → StrictAntiOn g (Icc 0 L) →
      0 < ∫ x in (0 : ℝ)..L, g x * φ x)
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * φ x = 0)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ AltComplement C uStar W := by
  rintro ⟨lam, w, hwW, hw0, hmem⟩
  have hne : (lam, uStar + w) ≠ (lamStar, uStar) := by
    intro h
    exact hw0 (by simpa using (Prod.ext_iff.mp h).2)
  have hprof : prof (uStar + w) = fun x => c + prof w x := by
    rw [map_add, hConst]; rfl
  have hzero := hW w hwW
  rcases hMono _ hmem hne with h | h
  · have hw : StrictAntiOn (prof w) (Icc 0 L) := by
      intro x hx y hy hxy
      have := h hx hy hxy
      simp only [hprof] at this
      linarith
    have := hφ _ (hCont w) hw
    linarith
  · have hw : StrictMonoOn (prof w) (Icc 0 L) := by
      intro x hx y hy hxy
      have := h hx hy hxy
      simp only [hprof] at this
      linarith
    have := hφ (fun x => -prof w x) (hCont w).neg
      (fun x hx y hy hxy => neg_lt_neg (hw hx hy hxy))
    simp only [neg_mul, intervalIntegral.integral_neg] at this
    linarith

/-- **Global unboundedness of a monotone branch.**  Let `C` be a unilateral
component whose points other than the bifurcation point `(λ*, u*)` have strictly
monotone profiles on `[0, L]`, as encoded by `hMono`.

Hypotheses kept explicit:
* `hAlt`: the global alternatives of Rabinowitz / Shi–Wang for `C`;
* `hMono`: strict monotonicity away from `(λ*, u*)` (for instance from
  `strictAntiOn_of_relClopen` or `strictMonoOn_of_relClopen`);
* `hφ`, `hW`: a weight `φ` pairing positively with continuous strictly
  decreasing profiles, to which the complement `W` is orthogonal;
* `hRelClosed`, `hCV`, `hCS`, `hAdmissible`: relative closedness in the
  admissible set and admissibility of limits;
* `hPrecompact`: relative compactness of bounded-parameter solution pieces.

Conclusions: alternatives (2) and (3) fail, `C` is not compact, and
`sup λ = +∞`. -/
theorem global_unbounded_of_monotone {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C S V : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hL : 0 < L)
    (hAlt : GlobalAlternatives C lamStar uStar W)
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
    ¬ AltOtherTrivial C lamStar uStar ∧ ¬ AltComplement C uStar W ∧
      ¬ IsCompact C ∧ (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  have hII := not_altOtherTrivial (c := c) hL hConst hMono
  have hIII := not_altComplement (lamStar := lamStar) hConst hCont hφ hW hMono
  have hNC := not_isCompact_of_alternatives hAlt hII hIII
  exact ⟨hII, hIII, hNC, sSup_param_eq_top hRelClosed hCV hCS hAdmissible hPrecompact hNC⟩

end Monotone

end ScalarPitchfork.Global
