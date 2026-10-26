<div align="center">

<img src="docs/assets/banner.svg" width="560" alt="The trivial branch splitting at the critical parameter into two branches of nontrivial zeros">

# Scalar Pitchfork

The scalar pitchfork $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$ with a remainder bounded by explicit weights or by jets at the origin: for small $`\tau`$ with $`\tau\beta>0`$, exactly one small zero of each sign, $`|z|=\sqrt{\alpha\tau/\beta}+O(|\tau|)`$, with the stability sign, lying on two branches continuous in $`\tau`$ when $`R`$ is continuous in $`\tau`$ (automatic under the jet hypotheses); no small nonzero zero when $`\tau\beta\le0`$; and the topological skeleton of global branches, with the global alternatives as hypotheses. Formalized in Lean 4 with Mathlib.

[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-56a0058-153e63)](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
[![Release](https://img.shields.io/badge/release-v0.1.0-153e63)](https://github.com/chenle02/scalar-pitchfork-lean/releases/tag/v0.1.0)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23498687.svg)](https://doi.org/10.5281/zenodo.23498687)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-153e63)](https://chenle02.github.io/scalar-pitchfork-lean/)

[Documentation site](https://chenle02.github.io/scalar-pitchfork-lean/) · [What is proved](docs/what-is-proved.md) · [Verification page](docs/verification.md) · [Build](#build-and-verify) · [Cite](CITATION.cff)

</div>

## What is proved

Here $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$ with parameter $`\tau`$ and amplitude $`z`$. Items 1–5
assume $`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`0<r\le1`$ and the **remainder bounds** on the box
$`|\tau|,|z|\le r`$:

```math
|R(\tau,z)|\le C\big(|z|\tau^2+|z|^3|\tau|+z^4\big),\qquad
\partial_zR(\tau,z)=R_z(\tau,z)\ \text{exists},\qquad
|R_z(\tau,z)|\le C\big(\tau^2+z^2|\tau|+|z|^3\big).
```

"For small $`\tau`$" means for all $`\tau`$ in some neighbourhood of $`0`$. Items 6–12 state their own
hypotheses. The results are classical
bifurcation theory in quantitative form; no new mathematics is claimed.

1. **[The two pitchfork branches](docs/what-is-proved.md#the-two-pitchfork-branches).** Assume the remainder bounds and that $`\tau\mapsto R(\tau,z)`$ is
   continuous at every $`|\tau|<r`$, $`|z|\le r`$. There are $`\rho>0`$, an open neighbourhood $`N`$ of $`0`$,
   a constant $`K`$ and, for $`\sigma=\pm1`$, functions $`b_\sigma`$ continuous on $`N`$ with $`b_\sigma(0)=0`$
   and $`b_\sigma(\tau)=0`$ for $`\tau\in N`$ with $`\tau\beta\le0`$, such that for $`\tau\in N`$ with $`\tau\beta>0`$: $`z=b_\sigma(\tau)`$
   is the unique zero of $`f(\tau,\cdot)`$ with $`\sigma z>0`$ and $`|z|\le\rho`$, it satisfies
   $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le K|\tau|`$, and $`\beta\,\partial_zf(\tau,z)<0`$. Every zero $`z\ne0`$
   with $`|z|\le\rho`$ and $`\tau\in N`$ has $`\tau\beta>0`$ and equals $`b_1(\tau)`$ or $`b_{-1}(\tau)`$.
   `ScalarPitchfork.pitchfork_branch_curves`
2. **[One signed zero at a fixed radius](docs/what-is-proved.md#one-signed-zero-at-a-fixed-radius).** Under the remainder bounds there is $`\rho>0`$ such that for small
   $`\tau`$ with $`\tau\beta>0`$ and each $`\sigma=\pm1`$, $`f(\tau,\cdot)`$ has exactly one zero $`z`$ with
   $`\sigma z>0`$ and $`|z|\le\rho`$.
   `ScalarPitchfork.existsUnique_branchRoot_eventually`
3. **[Existence with explicit amplitude constant](docs/what-is-proved.md#existence-of-both-branches-with-explicit-amplitude-constant-and-stability-sign).** Under the remainder bounds, for small $`\tau`$ with
   $`\tau\beta>0`$ and each $`\sigma=\pm1`$ there is a zero $`z`$ of $`f(\tau,\cdot)`$ with $`\sigma z>0`$,
   $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le K|\tau|`$ and $`\beta\,\partial_zf(\tau,z)<0`$, where
   $`K=2\alpha A\bigl(3|\beta|/(2\alpha)+1\bigr)/\beta^2`$ and $`A=C\bigl(2(|\beta|+2C)/\alpha+1\bigr)`$.
   `ScalarPitchfork.exists_branch_eventually`
4. **[Side and stability of every small zero](docs/what-is-proved.md#side-and-stability-of-every-small-nontrivial-zero).** Under the remainder bounds, every zero $`(\tau,z)`$ of $`f`$
   near $`(0,0)`$ with $`z\ne0`$ has $`\tau\beta>0`$ and $`\beta\,\partial_zf(\tau,z)<0`$.
   `ScalarPitchfork.branch_side_eventually`
5. **[At most one small zero of each sign](docs/what-is-proved.md#at-most-one-small-zero-of-each-sign).** Under the remainder bounds there is $`\rho>0`$ such that for
   small $`\tau`$, two zeros $`z_1,z_2`$ of $`f(\tau,\cdot)`$ with $`z_1z_2>0`$ and $`|z_1|,|z_2|\le\rho`$ are
   equal.
   `ScalarPitchfork.small_zero_eq_branch`
6. **[Exchange of stability on the exact cubic](docs/what-is-proved.md#exchange-of-stability-on-the-exact-cubic).** If $`\beta\ne0`$, $`A\ne0`$ and $`\alpha\tau A-\beta A^3=0`$,
   then $`\frac{d}{dA}(\alpha\tau A-\beta A^3)=-2\alpha\tau`$ at $`A`$.
   `ScalarPitchfork.deriv_cubicField_at_branch`
7. **[Square-root amplitude error](docs/what-is-proved.md#square-root-amplitude-error).** If $`\beta\ne0`$, $`z\ne0`$, $`\alpha\tau-\beta z^2+e=0`$,
   $`\alpha\tau/\beta\ge0`$ and $`|e|\le C|z|^3`$, then $`\bigl||z|-\sqrt{\alpha\tau/\beta}\bigr|\le Cz^2/|\beta|`$.
   `ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder`
8. **[Remainder bounds from jets](docs/what-is-proved.md#remainder-bounds-from-jets-at-the-origin).** Let $`R`$ be $`C^4`$ on an open set containing the box $`|\tau|,|z|\le r`$,
   with $`0<r\le1`$, let $`R(\tau,0)=0`$ for $`|\tau|\le r`$, and let
   $`\partial_zR=\partial_\tau\partial_zR=\partial_z^2R=\partial_\tau\partial_z^2R=\partial_z^3R=0`$ at the
   origin. Then the remainder bounds hold for some $`C\ge0`$, with $`R_z=\partial_zR`$, and
   $`\tau\mapsto R(\tau,z)`$ is continuous at every $`|\tau|<r`$, $`|z|\le r`$.
   `ScalarPitchfork.remainderBounds_of_jet`
9. **[Stronger bound iff the axis condition](docs/what-is-proved.md#the-stronger-remainder-bound-holds-iff-the-axis-condition-holds).** Under the hypotheses of item 8,
   $`|R(\tau,z)|\le C(z^2\tau^2+|z|^3|\tau|+z^4)`$ on the box for some $`C`$ if and only if
   $`\partial_zR(\tau,0)=0`$ for every $`|\tau|\le r`$.
   `ScalarPitchfork.strongBound_iff_axis`
10. **[Jets do not give the stronger bound](docs/what-is-proved.md#the-jets-at-the-origin-do-not-give-the-stronger-bound).** Not every $`R`$ satisfying the hypotheses of item 8 satisfies
    the stronger bound of item 9; the library's counterexample is $`R(\tau,z)=\tau^2z`$.
    `ScalarPitchfork.jet_not_sufficient_for_strongBound`
11. **[A non-compact component has unbounded parameter](docs/what-is-proved.md#a-non-compact-component-has-unbounded-parameter).** Let $`E`$ be a topological space and
    $`C\subseteq V\subseteq\mathbb R\times E`$ with $`C`$ relatively closed in $`V`$ and
    $`C\subseteq\overline S\subseteq V`$, where $`\overline{S\cap\{\lambda\le X\}}`$ is compact for every
    $`X\in\mathbb R`$. If $`C`$ is not compact, then $`C`$ contains points with arbitrarily large $`\lambda`$,
    and $`\sup\{\lambda:(\lambda,u)\in C\}=+\infty`$ in the extended reals.
    `ScalarPitchfork.Global.sSup_param_eq_top`
12. **[The one-sided component is closed](docs/what-is-proved.md#the-one-sided-component-is-closed).** Let $`S`$ be a closed subset of a topological space, $`b\in S`$,
    $`K`$ the connected component of $`b`$ in $`S`$, and $`A`$ a set whose trace on $`K`$ is relatively open in
    $`K`$. For $`s\in K\setminus A`$, the connected component of $`s`$ in $`K\setminus A`$ is closed.
    `ScalarPitchfork.Global.selectedComponent_isClosed`

Each Lean statement is the authority; read its hypotheses before you use it. The
[statement guide](docs/what-is-proved.md) gives these twelve headline results and five further groups (40
compared declarations in all), each with its exact Lean statement, source line and sign-off. The
[verification page](docs/verification.md) shows each Lean statement beside its description; the same page is
rendered in the [verification section](#verification-at-a-glance) at the end of this README.

The module map is on the [modules page](docs/modules.md).

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


The [Paper III source repository](https://github.com/chenle02/chemotaxis-paper-iii) and its
[Lean companion](https://github.com/chenle02/chemotaxis-paper-iii-lean) record the paper-specific
statements, hypotheses and verification boundaries. This standalone library exposes only the API
listed here. Later proofs in the companion do not automatically extend this library or certify the
whole paper. See the [result-by-result guide](docs/what-is-proved.md) for the existing library evidence.

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

**Related work**, and the libraries and tools this one builds on, are listed on the [acknowledgments page](docs/acknowledgments.md).

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
from the [modules page](docs/modules.md)). The trusted comparator statements are in
[`ScalarPitchfork/HeadlineChallenge.lean`](ScalarPitchfork/HeadlineChallenge.lean) (the twelve headline
results, configuration [`comparator.headline.json`](comparator.headline.json)) and
[`ScalarPitchfork/Challenge.lean`](ScalarPitchfork/Challenge.lean) (the full set, configuration
[`comparator.json`](comparator.json)); their `sorry` is intentional.
[`scripts/check-negative-controls.sh`](scripts/check-negative-controls.sh) checks that deliberately wrong
variants of the statements are rejected.

**Built on** Mathlib, Lean 4 and comparator; the full list with citations is on the [acknowledgments page](docs/acknowledgments.md#built-on).

## Trust and axioms

The library modules contain no `sorry`, `axiom`, `opaque` or `native_decide`; the build receipt at commit
`a460cf60cfe8` records `sorry` count 0 and the axioms `propext`, `Classical.choice` and `Quot.sound`, which are
the only permitted ones. The comparator checks that each proof proves exactly its Mathlib-only restatement:
the 12 headline statements in `HeadlineChallenge.lean` (`comparator.headline.json`) and the 40 statements of
the full set, which include those 12, in `Challenge.lean` (`comparator.json`); both pass, and independent
kernels replay the proofs. The `sorry` in the two Challenge files is intentional: they hold the statements,
not the proofs. No tool checks that the prose in this README describes the Lean statements. The recorded
results and receipts are in [What the checks establish](#what-the-checks-establish) at the end of this README.

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

The scalar reduction formalized here follows the analysis in the paper cited above by L. Chen, I. Ruau
and W. Shen; I thank both coauthors.

## Full verification record

The section below is generated by lean-pkg from `coverage.yaml`, `claims.yaml` and the committed receipts. It is easier to browse on the [documentation site](https://chenle02.github.io/scalar-pitchfork-lean/verification.html).

<details>
<summary><strong>Show the generated verification page</strong> (every result with its Lean statement, hypotheses and checks)</summary>

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page scalar-pitchfork-lean` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page scalar-pitchfork-lean --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

The scalar pitchfork f(tau, z) = alpha tau z - beta z^3 + R(tau, z) with a remainder bounded by weights or by jets: for small tau with tau beta &gt; 0, one small zero of each sign, square-root amplitude with O(\|tau\|) error and stability sign, on branches continuous when R is continuous in tau; remainder bounds from jets; the topological skeleton of global branches, alternatives assumed.

- Main results: 17; verified: 17 of 17.

## Main results

### The two pitchfork branches

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha>0$, $\beta\ne0$, $C\ge0$, $0<r\le1$ and $f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)$. Assume that for $|\tau|,|z|\le r$,
\[|R(\tau,z)|\le C\big(|z|\tau^2+|z|^3|\tau|+z^4\big),\qquad \partial_zR(\tau,z)=R_z(\tau,z),\qquad |R_z(\tau,z)|\le C\big(\tau^2+z^2|\tau|+|z|^3\big),\]
and that $\tau\mapsto R(\tau,z)$ is continuous at every $|\tau|<r$, $|z|\le r$. Then there are $\rho>0$, an open neighbourhood $N$ of $0$, $K\in\mathbb R$ and, for $\sigma\in\{1,-1\}$, functions $b_\sigma$ continuous on $N$ with $b_\sigma(0)=0$ and $b_\sigma(\tau)=0$ for $\tau\in N$ with $\tau\beta\le0$, such that for every $\tau\in N$ with $\tau\beta>0$: $f(\tau,\cdot)$ has exactly one zero $z$ with $\sigma z>0$ and $|z|\le\rho$; $z=b_\sigma(\tau)$ is that zero; $\big||b_\sigma(\tau)|-\sqrt{\alpha\tau/\beta}\big|\le K|\tau|$; and $\partial_zf(\tau,b_\sigma(\tau))\,\beta<0$. Moreover every $\tau\in N$ and $z\ne0$ with $|z|\le\rho$ and $f(\tau,z)=0$ satisfy $\tau\beta>0$ and $z\in\{b_1(\tau),b_{-1}(\tau)\}$.
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.pitchfork_branch_curves` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem pitchfork_branch_curves (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ K : ℝ, ∃ b : ℝ → ℝ → ℝ,
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ b sgn 0 = 0 ∧
          (∀ tau ∈ N, tau * beta ≤ 0 → b sgn tau = 0) ∧
          (∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0 ∧
            |(|b sgn tau| - Real.sqrt (alpha * tau / beta))| ≤ K * |tau| ∧
            deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) (b sgn tau) * beta < 0)) ∧
      (∀ tau ∈ N, ∀ z : ℝ, z ≠ 0 → |z| ≤ ρ → alpha * tau * z - beta * z ^ 3 + R tau z = 0 →
        0 < tau * beta ∧ (z = b 1 tau ∨ z = b (-1) tau))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### One signed zero at a fixed radius

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha>0$, $\beta\ne0$, $C\ge0$, $0<r\le1$, $f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)$, and let $R$ satisfy, for $|\tau|,|z|\le r$, $|R(\tau,z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)$, $\partial_zR(\tau,z)=R_z(\tau,z)$ and $|R_z(\tau,z)|\le C(\tau^2+z^2|\tau|+|z|^3)$. Then there is $\rho>0$ such that for all $\tau$ in a neighbourhood of $0$ with $\tau\beta>0$ and each $\sigma\in\{1,-1\}$,
\[\exists!\,z:\quad \sigma z>0,\quad |z|\le\rho,\quad f(\tau,z)=0.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.existsUnique_branchRoot_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem existsUnique_branchRoot_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta → ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Existence of both branches with explicit amplitude constant and stability sign

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the previous row, for all $\tau$ in a neighbourhood of $0$ with $\tau\beta>0$ and each $\sigma\in\{1,-1\}$ there is $z$ with $\sigma z>0$, $f(\tau,z)=0$, $\partial_zf(\tau,z)\,\beta<0$ and
\[\Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le K|\tau|,\qquad K=\frac{2\alpha A\big(\frac{3|\beta|}{2\alpha}+1\big)}{|\beta|^2},\quad A=C\Big(\frac{2(|\beta|+2C)}{\alpha}+1\Big).\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.exists_branch_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
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
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Side and stability of every small nontrivial zero

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the second row, for all $(\tau,z)$ in a neighbourhood of $(0,0)$,
\[z\ne0,\ f(\tau,z)=0\ \Longrightarrow\ \tau\beta>0\ \text{ and }\ \partial_zf(\tau,z)\,\beta<0.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.branch_side_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem branch_side_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), p.2 ≠ 0 →
      alpha * p.1 * p.2 - beta * p.2 ^ 3 + R p.1 p.2 = 0 →
        0 < p.1 * beta ∧
          deriv (fun z => alpha * p.1 * z - beta * z ^ 3 + R p.1 z) p.2 * beta < 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### At most one small zero of each sign

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the second row there is $\rho>0$ such that for all $\tau$ in a neighbourhood of $0$ and all $z_1,z_2\in\mathbb R$,
\[z_1z_2>0,\ |z_1|\le\rho,\ |z_2|\le\rho,\ f(\tau,z_1)=f(\tau,z_2)=0\ \Longrightarrow\ z_1=z_2.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.small_zero_eq_branch` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem small_zero_eq_branch (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ tau in 𝓝 (0 : ℝ), ∀ z₁ z₂ : ℝ, 0 < z₁ * z₂ → |z₁| ≤ ρ → |z₂| ≤ ρ →
      alpha * tau * z₁ - beta * z₁ ^ 3 + R tau z₁ = 0 →
      alpha * tau * z₂ - beta * z₂ ^ 3 + R tau z₂ = 0 → z₁ = z₂
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Exchange of stability on the exact cubic

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha,\beta,\tau,A\in\mathbb R$ with $\beta\ne0$, $A\ne0$ and $\alpha\tau A-\beta A^3=0$. Then
\[\frac{d}{dA'}\Big(\alpha\tau A'-\beta A'^3\Big)\Big|_{A'=A}=-2\alpha\tau.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.deriv_cubicField_at_branch` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem deriv_cubicField_at_branch (alpha beta tau A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    deriv (fun A => alpha * tau * A - beta * A ^ 3) A = -2 * alpha * tau
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Square-root amplitude error

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha,\beta,\tau,z,e,C\in\mathbb R$ with $\beta\ne0$, $z\ne0$, $\alpha\tau-\beta z^2+e=0$, $\alpha\tau/\beta\ge0$ and $|e|\le C|z|^3$. Then
\[\Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le\frac{Cz^2}{|\beta|}.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_sub_sqrt_le_of_cubic_remainder (alpha beta tau z e C : ℝ)
    (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (ht : 0 ≤ alpha * tau / beta) (herr : |e| ≤ C * |z| ^ 3) :
    |(|z| - Real.sqrt (alpha * tau / beta))| ≤ C * z ^ 2 / |beta|
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Remainder bounds from jets at the origin

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $0<r\le1$ and let $R:\mathbb R^2\to\mathbb R$ be $C^4$ on an open set $U$ containing the box $\{|\tau|,|z|\le r\}$. Assume $R(\tau,0)=0$ for $|\tau|\le r$ and
\[\partial_zR=\partial_\tau\partial_zR=\partial_z^2R=\partial_\tau\partial_z^2R=\partial_z^3R=0\quad\text{at }(0,0).\]
Then there is $C\ge0$ such that for $|\tau|,|z|\le r$: $|R(\tau,z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)$, $R(\tau,\cdot)$ has derivative $\partial_zR(\tau,z)$ at $z$, and $|\partial_zR(\tau,z)|\le C(\tau^2+z^2|\tau|+|z|^3)$; and $\tau\mapsto R(\tau,z)$ is continuous at every $|\tau|<r$, $|z|\le r$.
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.remainderBounds_of_jet` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem remainderBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (|z| * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        HasDerivAt (R e) (iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]) z) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        |iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]| ≤
          C * (e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) ∧
      (∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The stronger remainder bound holds iff the axis condition holds

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the previous row,
\[\Big(\exists C\ \forall\,|\tau|,|z|\le r:\ |R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big)\Big)\iff \partial_zR(\tau,0)=0\ \text{ for all }|\tau|\le r.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.strongBound_iff_axis` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem strongBound_iff_axis (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    (∃ C, ∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ↔
      ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 (Function.uncurry R) (e, 0) ![(0, 1)] = 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The jets at the origin do not give the stronger bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
It is not true that every $R$, $U$, $r$ satisfying the hypotheses of the row "Remainder bounds from jets at the origin" admit a constant $C$ with
\[|R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big)\quad\text{for all }|\tau|,|z|\le r.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.jet_not_sufficient_for_strongBound` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem jet_not_sufficient_for_strongBound :
    ¬ ∀ (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ),
      IsOpen U → ContDiffOn ℝ 4 (Function.uncurry R) U → 0 < r → r ≤ 1 →
      Metric.closedBall (0 : ℝ × ℝ) r ⊆ U → (∀ e, |e| ≤ r → R e 0 = 0) →
      iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0 →
      iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0 →
      iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0 →
      iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0 →
      iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0 →
      ∃ C, ∀ e z, |e| ≤ r → |z| ≤ r →
        |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### A non-compact component has unbounded parameter

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $E$ be a topological space and $C,S,V\subseteq\mathbb R\times E$ with $C\subseteq V$, $C$ closed in the subspace $V$, $C\subseteq\overline S\subseteq V$, and $\overline{S\cap\{(\lambda,u):\lambda\le X\}}$ compact for every $X\in\mathbb R$. If $C$ is not compact, then
\[\forall M\in\mathbb R\ \exists(\lambda,u)\in C:\ \lambda>M,\qquad \sup\{\lambda:(\lambda,u)\in C\}=+\infty\ \text{ in }\overline{\mathbb R}.\]
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.Global.sSup_param_eq_top` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem sSup_param_eq_top {E : Type*} [TopologicalSpace E] {C S V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The one-sided component is closed

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $X$ be a topological space, $S\subseteq X$ closed, $b\in S$, and $K$ the connected component of $b$ in $S$. Let $A\subseteq X$ with $A\cap K$ open in the subspace $K$, and let $s\in K\setminus A$. Then the connected component of $s$ in $K\setminus A$ is closed in $X$.
```

**In Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.Global.selectedComponent_isClosed` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem selectedComponent_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base selector : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen (((↑) : connectedComponentIn solutionClosure base → X) ⁻¹' removedArc))
    (hSelectorInRemainder :
      selector ∈ connectedComponentIn solutionClosure base \ removedArc) :
    IsClosed (connectedComponentIn
      (connectedComponentIn solutionClosure base \ removedArc) selector)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Pitchfork branches under the stronger remainder bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the row "Remainder bounds from jets at the origin" together with the axis condition $\partial_zR(\tau,0)=0$ for $|\tau|\le r$ (where $\partial_zR(\tau,z)=DR(\tau,z)(0,1)$), there is $C\ge0$ with, for $|\tau|,|z|\le r$,
\[|R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big),\qquad |\partial_zR(\tau,z)|\le C\big(|z|\tau^2+z^2|\tau|+|z|^3\big).\]
The axis condition holds for $R(\tau,z)=f(\tau,z)-\alpha\tau z+\beta z^3$ when $R$ satisfies those jet hypotheses and $\partial_zf(\tau,0)=\alpha\tau$ for $|\tau|\le r$; and if $\varphi'(0)=d$ and $|\varphi(z)|\le Kz^2$ for $|z|\le\delta$ with $\delta>0$, then $d=0$.
Let $\alpha>0$, $\beta\ne0$, $C\ge0$, $0<r\le1$, $f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)$, and assume for $|\tau|,|z|\le r$ the two stronger bounds above with $\partial_zR=R_z$. Then the conclusion of the row "Existence of both branches with explicit amplitude constant and stability sign" holds with the same constant $K$. If moreover $\tau\mapsto R(\tau,z)$ is continuous at every $|\tau|<r$, $|z|\le r$, there are $\rho>0$, an open neighbourhood $N$ of $0$ and, for $\sigma\in\{1,-1\}$, functions $b_\sigma$ continuous on $N$ with $b_\sigma(\tau)\to0$ as $\tau\to0$, such that for $\tau\in N$ with $\tau\beta>0$, $f(\tau,\cdot)$ has exactly one zero $z$ with $\sigma z>0$, $|z|\le\rho$, and $b_\sigma(\tau)$ is that zero.
At a single point: if $z\ne0$, $|z|,|\tau|\le1$, $2C|\tau|\le\alpha$, $\alpha\tau z-\beta z^3+R=0$, $d=\alpha\tau-3\beta z^2+R_s$, $|R|\le C(z^2\tau^2+|z|^3|\tau|+z^4)$, $|R_s|\le C(|z|\tau^2+z^2|\tau|+|z|^3)$ and $A(|\tau|+|z|)\le|\beta|/2$ with $A=C\big(\frac{2(|\beta|+2C)}{\alpha}+1\big)$, then $\tau\beta>0$, $d\beta<0$ and $\big||z|-\sqrt{\alpha\tau/\beta}\big|\le K|\tau|$.
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.strongBounds_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem strongBounds_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 (Function.uncurry R) (e, 0) ![(0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e z, |e| ≤ r → |z| ≤ r → |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4)) ∧
      (∀ e z, |e| ≤ r → |z| ≤ r →
        |iteratedFDeriv ℝ 1 (Function.uncurry R) (e, z) ![(0, 1)]| ≤
          C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.branch_eventually_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem branch_eventually_of_strongBound (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3)) :
    ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.branch_curves_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem branch_curves_of_strongBound (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e z, |e| ≤ r → |z| ≤ r →
      |R e z| ≤ C * (z ^ 2 * e ^ 2 + |z| ^ 3 * |e| + z ^ 4))
    (hRder : ∀ e z, |e| ≤ r → |z| ≤ r → HasDerivAt (R e) (Rs e z) z)
    (hRs : ∀ e z, |e| ≤ r → |z| ≤ r →
      |Rs e z| ≤ C * (|z| * e ^ 2 + z ^ 2 * |e| + |z| ^ 3))
    (hRcont : ∀ e z, |e| < r → |z| ≤ r → ContinuousAt (fun e' => R e' z) e) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ b : ℝ → ℝ → ℝ,
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ Tendsto (b sgn) (𝓝 0) (𝓝 0) ∧
          ∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.equilibrium_core_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem equilibrium_core_of_strongBound (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (z ^ 2 * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (|z| * tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : C * (2 * (|beta| + 2 * C) / alpha + 1) * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau|
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.deriv_zero_of_sq_bound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ z, |z| ≤ δ → |φ z| ≤ K * z ^ 2) : d = 0
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.axis_of_linearization` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem axis_of_linearization (alpha beta : ℝ) (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (hU : IsOpen U)
    (hsmooth : ContDiffOn ℝ 4
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → f e 0 - alpha * e * 0 + beta * 0 ^ 3 = 0)
    (hz : iteratedFDeriv ℝ 1
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) 0
        ![(0, 1), (0, 1), (0, 1)] = 0)
    (hlin : ∀ e, |e| ≤ r → HasDerivAt (f e) (alpha * e) 0) :
    ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1
      (Function.uncurry fun e z => f e z - alpha * e * z + beta * z ^ 3) (e, 0) ![(0, 1)] = 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Pitchfork branches directly from jets at the origin

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha>0$, $\beta\ne0$, and let $R$, $U$, $r$ satisfy the hypotheses of the row "Remainder bounds from jets at the origin" ($C^4$ on an open $U\supseteq\{|\tau|,|z|\le r\}$, $0<r\le1$, $R(\tau,0)=0$ for $|\tau|\le r$, and the five listed derivatives vanish at $(0,0)$); no remainder constant is assumed. Put $f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)$. Then the full conclusion of the row "The two pitchfork branches" holds for $f$ (with some $\rho>0$, open neighbourhood $N$ of $0$, $K$ and $b_{\pm1}$), and in addition $b_\sigma(\tau)\to0$ as $\tau\to0$. Moreover there is $C\ge0$ such that the conclusion of the row "Existence of both branches with explicit amplitude constant and stability sign" holds for $f$ with the explicit constant $K$ computed from this $C$.
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.pitchfork_branch_curves_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem pitchfork_branch_curves_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ))
    (r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ ρ > 0, ∃ N : Set ℝ, IsOpen N ∧ N ∈ 𝓝 (0 : ℝ) ∧ ∃ K : ℝ, ∃ b : ℝ → ℝ → ℝ,
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (b sgn) N ∧ b sgn 0 = 0 ∧ Tendsto (b sgn) (𝓝 0) (𝓝 0) ∧
          (∀ tau ∈ N, tau * beta ≤ 0 → b sgn tau = 0) ∧
          (∀ tau ∈ N, 0 < tau * beta →
            (∃! z, 0 < sgn * z ∧ |z| ≤ ρ ∧ alpha * tau * z - beta * z ^ 3 + R tau z = 0) ∧
            0 < sgn * b sgn tau ∧ |b sgn tau| ≤ ρ ∧
            alpha * tau * b sgn tau - beta * b sgn tau ^ 3 + R tau (b sgn tau) = 0 ∧
            |(|b sgn tau| - Real.sqrt (alpha * tau / beta))| ≤ K * |tau| ∧
            deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) (b sgn tau) * beta < 0)) ∧
      (∀ tau ∈ N, ∀ z : ℝ, z ≠ 0 → |z| ≤ ρ → alpha * tau * z - beta * z ^ 3 + R tau z = 0 →
        0 < tau * beta ∧ (z = b 1 tau ∨ z = b (-1) tau))
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.exists_branch_eventually_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_branch_eventually_of_jet (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ))
    (r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hU : IsOpen U) (hsmooth : ContDiffOn ℝ 4 (Function.uncurry R) U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbox : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U)
    (haxis : ∀ e, |e| ≤ r → R e 0 = 0)
    (hz : iteratedFDeriv ℝ 1 (Function.uncurry R) 0 ![(0, 1)] = 0)
    (htz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(1, 0), (0, 1)] = 0)
    (hzz : iteratedFDeriv ℝ 2 (Function.uncurry R) 0 ![(0, 1), (0, 1)] = 0)
    (htzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(1, 0), (0, 1), (0, 1)] = 0)
    (hzzz : iteratedFDeriv ℝ 3 (Function.uncurry R) 0 ![(0, 1), (0, 1), (0, 1)] = 0) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ tau in 𝓝 (0 : ℝ), 0 < tau * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ z, 0 < sgn * z ∧
        alpha * tau * z - beta * z ^ 3 + R tau z = 0 ∧
        |(|z| - Real.sqrt (alpha * tau / beta))| ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau| ∧
        deriv (fun z => alpha * tau * z - beta * z ^ 3 + R tau z) z * beta < 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Estimates at a single nontrivial equilibrium

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\alpha>0$, $\beta\ne0$, $C\ge0$, $z\ne0$, $|z|\le1$, $\alpha\tau z-\beta z^3+R=0$ and $d=\alpha\tau-3\beta z^2+R_s$ (real numbers). If $|R|\le C(|\tau||z|^3+z^4)$, $|R_s|\le C(|\tau|z^2+|z|^3)$ and $C(|\tau|+|z|)\le|\beta|/2$, then
\[\tau\beta>0,\qquad d\beta<0,\qquad \Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le\frac{2\alpha C\big(\frac{3|\beta|}{2\alpha}+1\big)}{|\beta|^2}|\tau|.\]
If instead $|\tau|\le1$, $2C|\tau|\le\alpha$, $|R|\le C(|z|\tau^2+|z|^3|\tau|+z^4)$, $|R_s|\le C(\tau^2+z^2|\tau|+|z|^3)$ and $A(|\tau|+|z|)\le|\beta|/2$ with $A=C\big(\frac{2(|\beta|+2C)}{\alpha}+1\big)$, the same holds with $C$ replaced by $A$ in the amplitude constant.
If $\alpha>0$, $\beta\ne0$, $A\ne0$ and $\alpha\tau A-\beta A^3=0$, then $A=\pm\sqrt{\alpha\tau/\beta}$. Finally, let $\alpha>0$, $\tau\beta>0$, $C\ge0$, let $R:\mathbb R\to\mathbb R$ be continuous on $\big[\sqrt{\alpha\tau/(2\beta)},\sqrt{2\alpha\tau/\beta}\big]$ with $|R(z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)$ for $0<z$, $z^2\le2\alpha\tau/\beta$, and $C\big(|\tau|+2\alpha\tau/\beta+2\alpha\sqrt{2\alpha\tau/\beta}/|\beta|\big)<\alpha/2$. Then there is $z>0$ with $\alpha\tau/(2\beta)\le z^2\le2\alpha\tau/\beta$ and $\alpha\tau z-\beta z^3+R(z)=0$.
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.perturbed_equilibrium_core` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem perturbed_equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hC : 0 ≤ C) (hs1 : |z| ≤ 1)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|tau| * |z| ^ 3 + |z| ^ 4))
    (hRs : |Rs| ≤ C * (|tau| * z ^ 2 + |z| ^ 3))
    (hrectangle : C * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau|
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.equilibrium_core` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem equilibrium_core (alpha beta tau z R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : z ≠ 0) (hC : 0 ≤ C)
    (hs1 : |z| ≤ 1) (heta1 : |tau| ≤ 1) (hetaC : 2 * C * |tau| ≤ alpha)
    (hroot : alpha * tau * z - beta * z ^ 3 + R = 0)
    (hderiv : ds = alpha * tau - 3 * beta * z ^ 2 + Rs)
    (hR : |R| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hRs : |Rs| ≤ C * (tau ^ 2 + z ^ 2 * |tau| + |z| ^ 3))
    (hrectangle : C * (2 * (|beta| + 2 * C) / alpha + 1) * (|tau| + |z|) ≤ |beta| / 2) :
    0 < tau * beta ∧ ds * beta < 0 ∧
      |(|z| - Real.sqrt (alpha * tau / beta))| ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |tau|
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.exists_pos_equilibrium` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_pos_equilibrium (alpha beta tau C : ℝ) (R : ℝ → ℝ)
    (halpha : 0 < alpha) (hside : 0 < tau * beta) (hC : 0 ≤ C)
    (hcont : ContinuousOn R
      (Set.Icc (Real.sqrt (alpha * tau / beta / 2)) (Real.sqrt (2 * (alpha * tau / beta)))))
    (hR : ∀ z, 0 < z → z ^ 2 ≤ 2 * (alpha * tau / beta) →
      |R z| ≤ C * (|z| * tau ^ 2 + |z| ^ 3 * |tau| + z ^ 4))
    (hsmall : C * (|tau| + 2 * (alpha * tau / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * tau / beta)) / |beta|) < alpha / 2) :
    ∃ z, 0 < z ∧ alpha * tau / beta / 2 ≤ z ^ 2 ∧ z ^ 2 ≤ 2 * (alpha * tau / beta) ∧
      alpha * tau * z - beta * z ^ 3 + R z = 0
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.nonzero_equilibrium_eq_branch` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem nonzero_equilibrium_eq_branch (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    A = Real.sqrt (alpha * tau / beta) ∨ A = -Real.sqrt (alpha * tau / beta)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Global alternatives under monotone profiles

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $E$ be a topological space with an additive commutative group structure (no continuity of the group operations is assumed), $P:E\to(\mathbb R\to\mathbb R)$ an additive map (the profile), $L>0$, $(\lambda^*,u^*)\in\mathbb R\times E$, $W\subseteq E$ and $C,S,V\subseteq\mathbb R\times E$. Assume the global alternatives: $C$ is not compact, or $(\lambda,u^*)\in C$ for some $\lambda\ne\lambda^*$, or $(\lambda,u^*+w)\in C$ for some $w\in W\setminus\{0\}$. Assume $P(u^*)$ is constant, every $P(e)$ is continuous on $[0,L]$, every $(\lambda,u)\in C\setminus\{(\lambda^*,u^*)\}$ has $P(u)$ strictly monotone on $[0,L]$, and the weight $\varphi$ satisfies
\[\int_0^Lg\,\varphi\,dx>0\ \text{ for every continuous strictly decreasing }g\text{ on }[0,L],\qquad \int_0^LP(w)\,\varphi\,dx=0\ \ (w\in W).\]
Then the second and third alternatives fail; if in addition $C$ satisfies the hypotheses of the row "A non-compact component has unbounded parameter" except non-compactness ($C\subseteq V$ relatively closed in $V$, $C\subseteq\overline S\subseteq V$, $\overline{S\cap\{\lambda\le X\}}$ compact for all $X$), then $C$ is not compact, has parameters $\lambda>M$ for every $M$, and $\sup\{\lambda:(\lambda,u)\in C\}=+\infty$.
Supporting facts: the alternatives with the last two excluded give non-compactness; if $C$ is closed, $C\subseteq\overline S$ and all $\overline{S\cap\{\lambda\le X\}}$ are compact, every slice $C\cap\{\lambda\le X\}$ is compact; if $C$ is preconnected, $p^*\in C\cap M$ and $C\cap M$ is clopen in $C$, then $C\subseteq M$; in particular, if $\{p\in C: p=p^*\text{ or }P(p_2)\text{ is strictly decreasing on }[0,L]\}$ is clopen in a preconnected $C\ni p^*$, every $p\in C\setminus\{p^*\}$ has strictly decreasing profile.
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.global_unbounded_of_monotone` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem global_unbounded_of_monotone {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C S V : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hL : 0 < L)
    (hAlt : ¬ IsCompact C ∨ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∨
      ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C)
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
    ¬ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∧
      ¬ (∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C) ∧
      ¬ IsCompact C ∧ (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_altComplement` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem not_altComplement {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} {W : Set E} {φ : ℝ → ℝ} (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hφ : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 L) → StrictAntiOn g (Icc 0 L) →
      0 < ∫ x in (0 : ℝ)..L, g x * φ x)
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * φ x = 0)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_altOtherTrivial` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem not_altOtherTrivial {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_isCompact_of_alternatives` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem not_isCompact_of_alternatives {E : Type*} [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {lamStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : ¬ IsCompact C ∨ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∨
      ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C)
    (hNotII : ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C)
    (hNotIII : ¬ ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C) :
    ¬ IsCompact C
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isCompact_slice` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem isCompact_slice {E : Type*} [TopologicalSpace E] {C S : Set (ℝ × E)}
    (hClosed : IsClosed C) (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar})
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.subset_of_relClopen` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem subset_of_relClopen {E : Type*} [TopologicalSpace E] {C M : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C) (hStarM : pStar ∈ M)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' M)) :
    C ⊆ M
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.strictAntiOn_of_relClopen` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem strictAntiOn_of_relClopen {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹'
      {p | p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)})) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Closedness and containment of one-sided components

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $X$ be a topological space. A connected component of a closed set $F$ (of a point of $F$) is closed, and if $P$ is closed and $A\cap P$ is open in the subspace $P$, then $P\setminus A$ is closed. Let $S\subseteq X$ be closed, $b\in S$ and $K$ the connected component of $b$ in $S$; then $K$ is closed, and $K\setminus A$ is closed whenever $A\cap K$ is open in the subspace $K$.
For any $A,A'\subseteq X$ and $s\in X$, the component $K_s$ of $s$ in $K\setminus A$ satisfies $K_s\subseteq S$. If $\{b\}\cup A'$ is connected and contained in $S$, then $\{b\}\cup A'\subseteq K$; if moreover $\{b\}\cup A'$ is disjoint from $A$, then $\{b\}\cup A'\subseteq K\setminus A$, and for every $s\in A'$,
\[\{b\}\cup A'\subseteq K_s,\qquad\text{in particular } b\in K_s.\]
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isClosed_connectedComponentIn_of_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X]
    {F : Set X} {x : X} (hF : IsClosed F) (hx : x ∈ F) :
    IsClosed (connectedComponentIn F x)
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isClosed_sdiff_of_isOpen_preimage` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem isClosed_sdiff_of_isOpen_preimage {X : Type*} [TopologicalSpace X]
    {parent removed : Set X} (hParent : IsClosed parent)
    (hRemoved : IsOpen (((↑) : parent → X) ⁻¹' removed)) :
    IsClosed (parent \ removed)
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.parentComponent_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem parentComponent_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure) :
    IsClosed (connectedComponentIn solutionClosure base)
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.unilateralRemainder_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem unilateralRemainder_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen (((↑) : connectedComponentIn solutionClosure base → X) ⁻¹' removedArc)) :
    IsClosed (connectedComponentIn solutionClosure base \ removedArc)
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_parentComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem retainedWithBase_subset_parentComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_unilateralRemainder` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem retainedWithBase_subset_unilateralRemainder {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base \ removedArc
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_selectedComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem retainedWithBase_subset_selectedComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc)
        selector
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.base_mem_selectedComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem base_mem_selectedComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    base ∈ connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc)
      selector
```

**In Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.selectedComponent_subset_solutionClosure` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem selectedComponent_subset_solutionClosure {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base selector : X} :
    connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc) selector ⊆
      solutionClosure
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 52 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 40 of 40 required claim(s) verified (`sha256:99271e7536a7de84…`).
- Build check (`lean-pkg gate`) at commit `a460cf60cfe8`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Statement comparison (comparator) at commit `a460cf60cfe8`: 2 configuration(s), 52 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/a460cf60cfe8-comparator.json` (used here) | statement comparison | `a460cf60cfe8` | 2026-10-20 | — | `0820b97aaabffd85098c0c29dac38940e2ab6cd3676fdaf6b6c15bf27fa2d9ec` |
| `.lean-receipts/a460cf60cfe8-slurm-5587784.json` (used here) | build | `a460cf60cfe8` | 2026-10-20 | slurm-5587784 | `59195a21a000ce35e63e98acb9d82288760e11702d9106e08bb41a30c793cfa3` |
| `.lean-receipts/a460cf60cfe8-slurm-5587785.json` | build | `a460cf60cfe8` | 2026-10-20 | slurm-5587785 | `dace652c9bef6ee306f62b270fc6d90ad7ed0d5d619698a498cf0fb8caedd288` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/scalar-pitchfork-lean
cd scalar-pitchfork-lean
git checkout a460cf60cfe88aa90019be59d45a1d0f14ece7e7   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *ScalarPitchfork: scalar pitchfork bifurcation with a jet-bounded remainder and the topology of global branches in Lean 4*. Version 0.1.0. [doi:10.5281/zenodo.23498687](https://doi.org/10.5281/zenodo.23498687).

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

<!-- lean-pkg:page:end -->

</details>
