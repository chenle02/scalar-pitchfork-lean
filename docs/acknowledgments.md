---
title: "Acknowledgments and citation"
description: "Authors, tools, compute and related work behind scalar-pitchfork-lean, and how to cite it."
---

# Acknowledgments and citation

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The Lean code was developed with AI assistance under the author's direction. Lean compilation and an
independent kernel comparison check the stated theorems only; AI assistance is not human mathematical
review. Mathlib retains its own notices (see [NOTICE](https://github.com/chenle02/scalar-pitchfork-lean/blob/main/NOTICE)).

The scalar reduction formalized here follows the analysis in the paper cited above by L. Chen, I. Ruau
and W. Shen; I thank both coauthors.

## lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)). The receipts under
[`.lean-receipts/`](https://github.com/chenle02/scalar-pitchfork-lean/tree/main/.lean-receipts/) bind the checks to a source commit, and the verification section below
is rendered by `lean-pkg page` from [`coverage.yaml`](https://github.com/chenle02/scalar-pitchfork-lean/blob/main/coverage.yaml), [`claims.yaml`](https://github.com/chenle02/scalar-pitchfork-lean/blob/main/claims.yaml) and those
receipts; `lean-pkg page scalar-pitchfork-lean --check` confirms it is current.

## Auburn University Easley Cluster

This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

The release build gates ran there as Slurm jobs; their receipts are committed under `.lean-receipts/` and listed on the [verification page](https://github.com/chenle02/scalar-pitchfork-lean/blob/main/verification.html).

## Built on

- [Mathlib](https://github.com/leanprover-community/mathlib4): The mathlib Community, *The Lean Mathematical
  Library*, CPP 2020, [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). The library
  uses Mathlib's intermediate value theorem, mean value inequality, compactness and `connectedComponentIn`
  API. Mathlib's implicit function theorem (including `implicitFunctionOfBivariate`) needs
  $`\partial_zf(0,0)\ne0`$, which fails at a pitchfork point, so the branches here are built from the
  intermediate value theorem and strict monotonicity instead; the jet-to-remainder bounds use the mean value
  inequality along segments rather than Mathlib's Taylor remainder theorems, and the global part uses the
  `connectedComponentIn` API rather than `connectedComponent_eq_iInter_isClopen`. Through Mathlib:
  [Batteries](https://github.com/leanprover-community/batteries),
  [Aesop](https://github.com/leanprover-community/aesop),
  [Qq](https://github.com/leanprover-community/quote4),
  [Plausible](https://github.com/leanprover-community/plausible),
  [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4),
  [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient),
  [import-graph](https://github.com/leanprover-community/import-graph) and
  [lean4-cli](https://github.com/leanprover/lean4-cli).
- [Lean 4](https://github.com/leanprover/lean4), including `leanchecker` (replay of the compiled proofs) and
  the `con-ron` kernel checker shipped in the toolchain.
- [comparator](https://github.com/leanprover/comparator) with
  [lean4export](https://github.com/leanprover/lean4export) and the
  [nanoda](https://github.com/robsimmons/nanoda_lib) kernel, for the statement comparison.


## Related work

These projects formalize nearby results. No code from them is used here.

- [jaumededios/Schiffer](https://github.com/jaumededios/Schiffer) (J. de Dios Pont and G. Cao-Labora), the
  closest prior art: a quantitative, contraction-certified rank-one Lyapunov–Schmidt reduction and an
  explicit-radius scalar branch with $`C^3`$ bounds under jet bounds, built for a planar counterexample to
  Schiffer's conjecture. It reaches the branch by factoring an odd reduced equation by the amplitude; this
  library works directly with the scalar normal form, a remainder that need not be odd, the square-root
  amplitude, the stability sign and the jet counterexample. The repository has no license.
- The crnt-lean project ([github.com/marpaia/crnt-lean](https://github.com/marpaia/crnt-lean)): Hopf
  crossing conditions, the planar Poincaré normal form with its first Lyapunov coefficient and the limit
  cycle of the truncated cubic radial normal form, and persistence of the amplitude at a nondegenerate root
  by Mathlib's implicit function theorem; the averaged radial field of the full system is taken as data.
- [Arthur742Ramos/boundary-bumping-lean](https://github.com/Arthur742Ramos/boundary-bumping-lean): boundary
  bumping in compact connected Hausdorff spaces, including the clopen separation step that a Whyburn-type
  argument needs.
- [LeanCert](https://github.com/alerad/leancert) (interval arithmetic, certified roots) and
  [leanprover/hex](https://github.com/leanprover/hex) (verified computational algebra, root isolation) give
  certified roots of specific functions. They are not used here.
- In Isabelle/HOL, the [Ordinary Differential Equations](https://isa-afp.org/entries/Ordinary_Differential_Equations.html)
  entry of the Archive of Formal Proofs (F. Immler and J. Hölzl) formalizes flows and their dependence on
  data; it does not treat bifurcation.

As of October 2026 we found no machine-checked Crandall–Rabinowitz theorem, Rabinowitz global alternative,
Whyburn lemma or Leray–Schauder degree in Mathlib, the Reservoir package index, the Palomar index or the other
proof assistants we searched. This is a bounded search, not a claim that none exists.


## How to cite

Cite the software with [CITATION.cff](https://github.com/chenle02/scalar-pitchfork-lean/blob/main/CITATION.cff) ([doi:10.5281/zenodo.23498687](https://doi.org/10.5281/zenodo.23498687)).
