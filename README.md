<div align="center">

# Scalar Pitchfork

The scalar pitchfork $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$ with a remainder bounded by explicit weights or by jets at the origin: two continuous branches $`z\approx\pm\sqrt{\alpha\tau/\beta}`$ with an $`O(|\tau|)`$ amplitude error and the stability sign, the classification of small zeros, and the topological skeleton of global branches. Formalized in Lean 4 with Mathlib.

[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-153e63)](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
[![Version](https://img.shields.io/badge/version-0.1.0-153e63)](CITATION.cff)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)

[What is proved](#what-is-proved) · [Verification page](docs/verification.md) · [Build](#build-and-verify) · [Cite](CITATION.cff)

</div>

## What is proved

Throughout, $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$ with parameter $`\tau`$ and amplitude $`z`$, and
$`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`0<r\le1`$. Items 1-5 assume the **remainder bounds** on the box
$`|\tau|,|z|\le r`$:

```math
|R(\tau,z)|\le C\big(|z|\tau^2+|z|^3|\tau|+z^4\big),\qquad
\partial_zR(\tau,z)=R_z(\tau,z)\ \text{exists},\qquad
|R_z(\tau,z)|\le C\big(\tau^2+z^2|\tau|+|z|^3\big).
```

"For small $`\tau`$" means for all $`\tau`$ in some neighbourhood of $`0`$. The results are classical
bifurcation theory in quantitative form; no new mathematics is claimed.

1. **The two pitchfork branches.** Assume the remainder bounds and that $`\tau\mapsto R(\tau,z)`$ is
   continuous at every $`|\tau|<r`$, $`|z|\le r`$. There are $`\rho>0`$, an open neighbourhood $`N`$ of $`0`$,
   a constant $`K`$ and, for $`\sigma=\pm1`$, functions $`b_\sigma`$ continuous on $`N`$ with $`b_\sigma(0)=0`$
   and $`b_\sigma(\tau)=0`$ for $`\tau\in N`$ with $`\tau\beta\le0`$, such that for $`\tau\in N`$ with $`\tau\beta>0`$: $`z=b_\sigma(\tau)`$
   is the unique zero of $`f(\tau,\cdot)`$ with $`\sigma z>0`$ and $`|z|\le\rho`$, it satisfies
   $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le K|\tau|`$, and $`\beta\,\partial_zf(\tau,z)<0`$. Every zero $`z\ne0`$
   with $`|z|\le\rho`$ and $`\tau\in N`$ has $`\tau\beta>0`$ and equals $`b_1(\tau)`$ or $`b_{-1}(\tau)`$.
   `ScalarPitchfork.pitchfork_branch_curves`
2. **One signed zero at a fixed radius.** Under the remainder bounds there is $`\rho>0`$ such that for small
   $`\tau`$ with $`\tau\beta>0`$ and each $`\sigma=\pm1`$, $`f(\tau,\cdot)`$ has exactly one zero $`z`$ with
   $`\sigma z>0`$ and $`|z|\le\rho`$.
   `ScalarPitchfork.existsUnique_branchRoot_eventually`
3. **Existence with explicit amplitude constant.** Under the remainder bounds, for small $`\tau`$ with
   $`\tau\beta>0`$ and each $`\sigma=\pm1`$ there is a zero $`z`$ of $`f(\tau,\cdot)`$ with $`\sigma z>0`$,
   $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le K|\tau|`$ and $`\beta\,\partial_zf(\tau,z)<0`$, where
   $`K=2\alpha A\bigl(3|\beta|/(2\alpha)+1\bigr)/\beta^2`$ and $`A=C\bigl(2(|\beta|+2C)/\alpha+1\bigr)`$.
   `ScalarPitchfork.exists_branch_eventually`
4. **Side and stability of every small zero.** Under the remainder bounds, every zero $`(\tau,z)`$ of $`f`$
   near $`(0,0)`$ with $`z\ne0`$ has $`\tau\beta>0`$ and $`\beta\,\partial_zf(\tau,z)<0`$.
   `ScalarPitchfork.branch_side_eventually`
5. **At most one small zero of each sign.** Under the remainder bounds there is $`\rho>0`$ such that for
   small $`\tau`$, two zeros $`z_1,z_2`$ of $`f(\tau,\cdot)`$ with $`z_1z_2>0`$ and $`|z_1|,|z_2|\le\rho`$ are
   equal.
   `ScalarPitchfork.small_zero_eq_branch`
6. **Exchange of stability on the exact cubic.** If $`\beta\ne0`$, $`A\ne0`$ and $`\alpha\tau A-\beta A^3=0`$,
   then $`\frac{d}{dA}(\alpha\tau A-\beta A^3)=-2\alpha\tau`$ at $`A`$.
   `ScalarPitchfork.deriv_cubicField_at_branch`
7. **Square-root amplitude error.** If $`\beta\ne0`$, $`z\ne0`$, $`\alpha\tau-\beta z^2+e=0`$,
   $`\alpha\tau/\beta\ge0`$ and $`|e|\le C|z|^3`$, then $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le Cz^2/|\beta|`$.
   `ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder`
8. **Remainder bounds from jets.** Let $`R`$ be $`C^4`$ on an open set containing the box $`|\tau|,|z|\le r`$,
   with $`0<r\le1`$, let $`R(\tau,0)=0`$ for $`|\tau|\le r`$, and let
   $`\partial_zR=\partial_\tau\partial_zR=\partial_z^2R=\partial_\tau\partial_z^2R=\partial_z^3R=0`$ at the
   origin. Then the remainder bounds hold for some $`C\ge0`$, with $`R_z=\partial_zR`$, and
   $`\tau\mapsto R(\tau,z)`$ is continuous at every $`|\tau|<r`$, $`|z|\le r`$.
   `ScalarPitchfork.remainderBounds_of_jet`
9. **Stronger bound iff the axis condition.** Under the hypotheses of item 8,
   $`|R(\tau,z)|\le C(z^2\tau^2+|z|^3|\tau|+z^4)`$ on the box for some $`C`$ if and only if
   $`\partial_zR(\tau,0)=0`$ for every $`|\tau|\le r`$.
   `ScalarPitchfork.strongBound_iff_axis`
10. **Jets do not give the stronger bound.** Not every $`R`$ satisfying the hypotheses of item 8 satisfies
    the stronger bound of item 9; the library's counterexample is $`R(\tau,z)=\tau^2z`$.
    `ScalarPitchfork.jet_not_sufficient_for_strongBound`
11. **A non-compact component has unbounded parameter.** Let $`E`$ be a topological space and
    $`C\subseteq V\subseteq\mathbb R\times E`$ with $`C`$ relatively closed in $`V`$ and
    $`C\subseteq\overline S\subseteq V`$, where $`\overline{S\cap\{\lambda\le X\}}`$ is compact for every
    $`X\in\mathbb R`$. If $`C`$ is not compact, then $`C`$ contains points with arbitrarily large $`\lambda`$,
    and $`\sup\{\lambda:(\lambda,u)\in C\}=+\infty`$ in the extended reals.
    `ScalarPitchfork.Global.sSup_param_eq_top`
12. **The one-sided component is closed.** Let $`S`$ be a closed subset of a topological space, $`b\in S`$,
    $`K`$ the connected component of $`b`$ in $`S`$, and $`A`$ a set whose trace on $`K`$ is relatively open in
    $`K`$. For $`s\in K\setminus A`$, the connected component of $`s`$ in $`K\setminus A`$ is closed.
    `ScalarPitchfork.Global.selectedComponent_isClosed`

Each Lean statement is the authority; read its hypotheses before you use it. The
[verification page](docs/verification.md) shows each Lean statement beside its description; the same page is
rendered in the verification section at the end of this README.

| Module | Contents |
|---|---|
| `ScalarPitchfork.Cubic` | The exact cubic $`\alpha\tau A-\beta A^3`$: nonzero zeros $`\pm\sqrt{\alpha\tau/\beta}`$ on the side $`\tau\beta>0`$, derivative $`-2\alpha\tau`$ there |
| `ScalarPitchfork.Perturbed` | At a given nonzero zero of a perturbed cubic: side, derivative sign, square-root amplitude error |
| `ScalarPitchfork.Existence` | The field `pitchforkField`; both signed branches exist under the remainder bounds (intermediate value theorem), side and stability of every small zero |
| `ScalarPitchfork.Branch` | Uniqueness in a fixed window, classification of small zeros, continuity of the branch functions; packaged in `pitchfork_branch_curves` |
| `ScalarPitchfork.StrongRemainder` | The stronger remainder bound implies the weak one; the branch theorems transfer |
| `ScalarPitchfork.Jet` | `PitchforkJet`: $`C^4`$, the axis condition and five vanishing jets give the remainder bounds; the stronger bound holds iff $`\partial_zR(\tau,0)=0`$; branch theorems from jets |
| `ScalarPitchfork.JetCounterexample` | $`R=\tau^2z`$: the jets do not give the stronger bound; the axis condition from an exact linearization |
| `ScalarPitchfork.Global.Alternatives` | The three global alternatives as hypotheses: elimination, closedness, unbounded parameter, connectedness propagation, exclusion for strictly monotone profiles |
| `ScalarPitchfork.Global.ComponentClosure` | Parent component, one-sided remainder and selected component of a solution set; closedness |

> [!IMPORTANT]
> **Not proved here.**
> - No Crandall–Rabinowitz theorem and no center-manifold reduction: the scalar normal form $`\alpha\tau z-\beta z^3+R`$ is the starting point, not derived from an operator equation.
> - No Lyapunov–Schmidt reduction.
> - No degree theory: no Leray–Schauder degree and no Rabinowitz global alternative. The global part is the topological skeleton only; the alternatives are hypotheses, not derived from degree theory.
> - No certified-root tools: no interval arithmetic or root isolation for specific polynomials.
> - No PDE: no existence, uniqueness or regularity theorem for any differential equation.

## Paper and references

The library was first developed for the Lean companion of the paper below. It keeps only the general
mathematics; nothing in the library depends on the paper.

L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent sensitivity and a logistic-type
source, III: Bifurcation and spike-like solutions*, preprint, 2026.
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976).

```bibtex
@article{chen.ruau.ea:26:bifurcation,
  title         = {Chemotaxis models with signal-dependent sensitivity and a logistic-type source, {III}: Bifurcation and spike-like solutions},
  author        = {Chen, Le and Ruau, Ian and Shen, Wenxian},
  year          = {2026},
  month         = {October},
  journal       = {Preprint arXiv:2610.20976},
  eprint        = {2610.20976},
  archiveprefix = {arXiv},
  primaryclass  = {math.AP},
  url           = {https://arxiv.org/abs/2610.20976}
}
```

A sibling library from the same companion is
[neumann-cosine-lean](https://github.com/chenle02/neumann-cosine-lean)
([doi:10.5281/zenodo.23488175](https://doi.org/10.5281/zenodo.23488175)): Neumann cosine series on an
interval and the discrete Neumann Laplacian. The two libraries are independent.

The local results concern the scalar equation that a Crandall–Rabinowitz or center-manifold reduction
produces, and the global part follows the structure of Rabinowitz's global alternative and its unilateral
form: M. G. Crandall and P. H. Rabinowitz, *Bifurcation from simple eigenvalues*, J. Funct. Anal. 8 (1971),
321–340, [doi:10.1016/0022-1236(71)90015-2](https://doi.org/10.1016/0022-1236(71)90015-2);
P. H. Rabinowitz, *Some global results for nonlinear eigenvalue problems*, J. Funct. Anal. 7 (1971),
487–513, [doi:10.1016/0022-1236(71)90030-9](https://doi.org/10.1016/0022-1236(71)90030-9);
J. Shi and X. Wang, *On global bifurcation for quasilinear elliptic systems on bounded domains*,
J. Differential Equations 246 (2009), 2788–2812,
[doi:10.1016/j.jde.2008.09.009](https://doi.org/10.1016/j.jde.2008.09.009). None of these theorems is
formalized here.

**Related work.** These projects formalize nearby results. No code from them is used here.

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

## Build and verify

Toolchain Lean `v4.35.0` ([`lean-toolchain`](lean-toolchain)); Mathlib `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` ([`lake-manifest.json`](lake-manifest.json)).

```sh
git clone https://github.com/chenle02/scalar-pitchfork-lean.git
cd scalar-pitchfork-lean
lake exe cache get
lake build
```

To use it from another Lake project with the same toolchain:

```toml
[[require]]
name = "scalar-pitchfork-lean"
git = "https://github.com/chenle02/scalar-pitchfork-lean.git"
rev = "v0.1.0"
```

then `lake update scalar-pitchfork-lean`, `lake exe cache get`, and `import ScalarPitchfork` (or one module
from the table above). The trusted comparator statements are in
[`ScalarPitchfork/HeadlineChallenge.lean`](ScalarPitchfork/HeadlineChallenge.lean) (the twelve headline
results, configuration [`comparator.headline.json`](comparator.headline.json)) and
[`ScalarPitchfork/Challenge.lean`](ScalarPitchfork/Challenge.lean) (the full set, configuration
[`comparator.json`](comparator.json)); their `sorry` is intentional.
[`scripts/check-negative-controls.sh`](scripts/check-negative-controls.sh) checks that deliberately wrong
variants of the statements are rejected.

**Built on.**

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

## Trust and axioms

The library modules contain no `sorry`, `axiom`, `opaque` or `native_decide`. The permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`. The comparator checks that each headline proof proves exactly
its Mathlib-only restatement in `HeadlineChallenge.lean` (and `Challenge.lean` for the full set), and
independent kernels replay it. No tool checks that the prose in this README describes the Lean statements.
The recorded results and receipts are in the verification section at the end of this README.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)). The receipts under
[`.lean-receipts/`](.lean-receipts/) bind the checks to a source commit, and the verification section below
is rendered by `lean-pkg page` from [`coverage.yaml`](coverage.yaml), [`claims.yaml`](claims.yaml) and those
receipts; `lean-pkg page scalar-pitchfork-lean --check` confirms it is current.

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The Lean code was developed with AI assistance under the author's direction. Lean compilation and an
independent kernel comparison check the stated theorems only; AI assistance is not human mathematical
review. Mathlib retains its own notices (see [NOTICE](NOTICE)).

<!-- lean-pkg:page:begin -->
<!-- lean-pkg:page:end -->
