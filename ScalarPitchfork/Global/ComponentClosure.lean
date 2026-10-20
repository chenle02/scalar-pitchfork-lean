/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Constructions

/-!
# Closedness of a unilateral connected component

In unilateral global bifurcation theory (Rabinowitz; Shi–Wang) one splits the
connected component of the nontrivial-solution set through a bifurcation point
into two halves by deleting one of the two local half-branches, and then takes
the connected component of what remains.  This file isolates the purely
topological part of that construction on an arbitrary topological space `X`
(typically an admissible open set with its subspace topology):

* `parentComponent`: the component of the solution set through the base point;
* `unilateralRemainder`: the parent component minus the opposite half-branch;
* `selectedComponent`: the component of the remainder through a point of the
  retained half-branch.

The main result `selectedComponent_isClosed` shows that the unilateral
component is closed as soon as the solution set is closed and the removed
half-branch is relatively open in the parent component.  The local bifurcation
geometry enters only through explicit openness, connectedness, containment and
disjointness hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace ScalarPitchfork.Global

open Set

section

variable {X : Type*} [TopologicalSpace X]

/-- The parent component: the connected component of the closed set of
nontrivial solutions that contains the bifurcation point `base`. -/
noncomputable def parentComponent (solutionClosure : Set X) (base : X) : Set X :=
  connectedComponentIn solutionClosure base

/-- The unilateral remainder: the parent component with the opposite punctured
local half-branch `removedArc` removed. -/
noncomputable def unilateralRemainder
    (solutionClosure removedArc : Set X) (base : X) : Set X :=
  parentComponent solutionClosure base \ removedArc

/-- The unilateral component: the connected component of the unilateral
remainder containing a point `selector` of the retained local half-branch. -/
noncomputable def selectedComponent
    (solutionClosure removedArc : Set X) (base selector : X) : Set X :=
  connectedComponentIn (unilateralRemainder solutionClosure removedArc base) selector

/-- A connected component inside a closed subset is closed in the ambient
space.  This is obtained from the closed component in the subtype and the
closed subtype inclusion. -/
theorem isClosed_connectedComponentIn_of_isClosed
    {F : Set X} {x : X} (hF : IsClosed F) (hx : x ∈ F) :
    IsClosed (connectedComponentIn F x) := by
  rw [connectedComponentIn_eq_image hx]
  exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent

/-- Removing a set open in the relative topology of a closed parent leaves a
set closed in the ambient space. -/
theorem isClosed_sdiff_of_isOpen_preimage
    {parent removed : Set X} (hParent : IsClosed parent)
    (hRemoved : IsOpen (((↑) : parent → X) ⁻¹' removed)) :
    IsClosed (parent \ removed) := by
  have hImage :
      ((↑) : parent → X) '' ((((↑) : parent → X) ⁻¹' removed)ᶜ) =
        parent \ removed := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, by simpa using hz⟩
    · rintro ⟨hyParent, hyRemoved⟩
      exact ⟨⟨y, hyParent⟩, by simpa, rfl⟩
  rw [← hImage]
  exact hParent.isClosedMap_subtype_val _ hRemoved.isClosed_compl

/-- The parent component is closed once the set of nontrivial solutions is
closed. -/
theorem parentComponent_isClosed
    {solutionClosure : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure) :
    IsClosed (parentComponent solutionClosure base) := by
  exact isClosed_connectedComponentIn_of_isClosed hSolutionClosed hBase

/-- If the opposite half-branch is open in the relative topology of the parent
component (an input from the local bifurcation analysis), the unilateral
remainder is closed. -/
theorem unilateralRemainder_isClosed
    {solutionClosure removedArc : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen
        (((↑) : parentComponent solutionClosure base → X) ⁻¹' removedArc)) :
    IsClosed (unilateralRemainder solutionClosure removedArc base) := by
  exact isClosed_sdiff_of_isOpen_preimage
    (parentComponent_isClosed hSolutionClosed hBase) hRemovedRelOpen

/-- A connected retained half-branch together with the bifurcation point lies in
the parent component when it lies in the solution set. -/
theorem retainedWithBase_subset_parentComponent
    {solutionClosure retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure) :
    insert base retainedArc ⊆ parentComponent solutionClosure base := by
  exact hRetainedConnected.isPreconnected.subset_connectedComponentIn
    (mem_insert base retainedArc) hRetainedInSolution

/-- If the retained local half-branch and the base point avoid the removed
opposite half-branch, they lie in the unilateral remainder. -/
theorem retainedWithBase_subset_unilateralRemainder
    {solutionClosure removedArc retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      unilateralRemainder solutionClosure removedArc base := by
  intro x hx
  exact ⟨retainedWithBase_subset_parentComponent hRetainedConnected
    hRetainedInSolution hx, Set.disjoint_left.mp hAvoidRemoved hx⟩

/-- The connected retained local half-branch selects a single component of the
remainder: both the punctured half-branch and its limiting base point belong to
the selected component. -/
theorem retainedWithBase_subset_selectedComponent
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      selectedComponent solutionClosure removedArc base selector := by
  have hSubset : insert base retainedArc ⊆
      unilateralRemainder solutionClosure removedArc base :=
    retainedWithBase_subset_unilateralRemainder hRetainedConnected
      hRetainedInSolution hAvoidRemoved
  exact hRetainedConnected.isPreconnected.subset_connectedComponentIn
    (mem_insert_of_mem base hSelector) hSubset

/-- In particular, the bifurcation point belongs to the unilateral component
selected by any point of the retained half-branch. -/
theorem base_mem_selectedComponent
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    base ∈ selectedComponent solutionClosure removedArc base selector := by
  exact retainedWithBase_subset_selectedComponent hSelector hRetainedConnected
    hRetainedInSolution hAvoidRemoved (mem_insert base retainedArc)

/-- The unilateral component is closed.  Beyond closedness of the solution set,
the only input is relative openness of the removed opposite half-branch in the
parent component. -/
theorem selectedComponent_isClosed
    {solutionClosure removedArc : Set X} {base selector : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen
        (((↑) : parentComponent solutionClosure base → X) ⁻¹' removedArc))
    (hSelectorInRemainder :
      selector ∈ unilateralRemainder solutionClosure removedArc base) :
    IsClosed (selectedComponent solutionClosure removedArc base selector) := by
  exact isClosed_connectedComponentIn_of_isClosed
    (unilateralRemainder_isClosed hSolutionClosed hBase hRemovedRelOpen)
    hSelectorInRemainder

/-- The unilateral component lies inside the solution set. -/
theorem selectedComponent_subset_solutionClosure
    {solutionClosure removedArc : Set X} {base selector : X} :
    selectedComponent solutionClosure removedArc base selector ⊆ solutionClosure := by
  exact (connectedComponentIn_subset _ _).trans
    (sdiff_subset.trans (connectedComponentIn_subset _ _))

end

end ScalarPitchfork.Global
