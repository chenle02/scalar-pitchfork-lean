# What is proved

This guide presents the existing `scalar-pitchfork-lean` results with their exact compared Lean statements.
The proofs are classical mathematics. Their application to a particular differential equation requires
checking that equation's hypotheses separately.

## Notation and scope

The scalar field is `alpha*tau*z - beta*z^3 + R(tau,z)`. Branch results require the stated parameter signs, regularity and quantitative remainder bounds. Global component results take compactness, relative openness or global alternatives as explicit hypotheses where shown; they do not establish degree theory.

| Result | Evidence |
|---|---|
| The two pitchfork branches | Compared statement; existing release receipts |
| One signed zero at a fixed radius | Compared statement; existing release receipts |
| Existence of both branches with explicit amplitude constant and stability sign | Compared statement; existing release receipts |
| Side and stability of every small nontrivial zero | Compared statement; existing release receipts |
| At most one small zero of each sign | Compared statement; existing release receipts |
| Exchange of stability on the exact cubic | Compared statement; existing release receipts |
| Square-root amplitude error | Compared statement; existing release receipts |
| Remainder bounds from jets at the origin | Compared statement; existing release receipts |
| The stronger remainder bound holds iff the axis condition holds | Compared statement; existing release receipts |
| The jets at the origin do not give the stronger bound | Compared statement; existing release receipts |
| A non-compact component has unbounded parameter | Compared statement; existing release receipts |
| The one-sided component is closed | Compared statement; existing release receipts |
| Pitchfork branches under the stronger remainder bound | Compared statement; existing release receipts |
| Pitchfork branches directly from jets at the origin | Compared statement; existing release receipts |
| Estimates at a single nontrivial equilibrium | Compared statement; existing release receipts |
| Global alternatives under monotone profiles | Compared statement; existing release receipts |
| Closedness and containment of one-sided components | Compared statement; existing release receipts |

## Results

### The two pitchfork branches

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`0<r\le1`$ and $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$. Assume that for $`|\tau|,|z|\le r`$,


```math
|R(\tau,z)|\le C\big(|z|\tau^2+|z|^3|\tau|+z^4\big),\qquad \partial_zR(\tau,z)=R_z(\tau,z),\qquad |R_z(\tau,z)|\le C\big(\tau^2+z^2|\tau|+|z|^3\big),
```


and that $`\tau\mapsto R(\tau,z)`$ is continuous at every $`|\tau|<r`$, $`|z|\le r`$. Then there are $`\rho>0`$, an open neighbourhood $`N`$ of $`0`$, $`K\in\mathbb R`$ and, for $`\sigma\in\{1,-1\}`$, functions $`b_\sigma`$ continuous on $`N`$ with $`b_\sigma(0)=0`$ and $`b_\sigma(\tau)=0`$ for $`\tau\in N`$ with $`\tau\beta\le0`$, such that for every $`\tau\in N`$ with $`\tau\beta>0`$: $`f(\tau,\cdot)`$ has exactly one zero $`z`$ with $`\sigma z>0`$ and $`|z|\le\rho`$; $`z=b_\sigma(\tau)`$ is that zero; $`\big||b_\sigma(\tau)|-\sqrt{\alpha\tau/\beta}\big|\le K|\tau|`$; and $`\partial_zf(\tau,b_\sigma(\tau))\,\beta<0`$. Moreover every $`\tau\in N`$ and $`z\ne0`$ with $`|z|\le\rho`$ and $`f(\tau,z)=0`$ satisfy $`\tau\beta>0`$ and $`z\in\{b_1(\tau),b_{-1}(\tau)\}`$.


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.pitchfork_branch_curves` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L52): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### One signed zero at a fixed radius

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`0<r\le1`$, $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$, and let $`R`$ satisfy, for $`|\tau|,|z|\le r`$, $`|R(\tau,z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)`$, $`\partial_zR(\tau,z)=R_z(\tau,z)`$ and $`|R_z(\tau,z)|\le C(\tau^2+z^2|\tau|+|z|^3)`$. Then there is $`\rho>0`$ such that for all $`\tau`$ in a neighbourhood of $`0`$ with $`\tau\beta>0`$ and each $`\sigma\in\{1,-1\}`$,


```math
\exists!\,z:\quad \sigma z>0,\quad |z|\le\rho,\quad f(\tau,z)=0.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.existsUnique_branchRoot_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L81): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Existence of both branches with explicit amplitude constant and stability sign

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the previous row, for all $`\tau`$ in a neighbourhood of $`0`$ with $`\tau\beta>0`$ and each $`\sigma\in\{1,-1\}`$ there is $`z`$ with $`\sigma z>0`$, $`f(\tau,z)=0`$, $`\partial_zf(\tau,z)\,\beta<0`$ and


```math
\Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le K|\tau|,\qquad K=\frac{2\alpha A\big(\frac{3|\beta|}{2\alpha}+1\big)}{|\beta|^2},\quad A=C\Big(\frac{2(|\beta|+2C)}{\alpha}+1\Big).
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.exists_branch_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L101): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Side and stability of every small nontrivial zero

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the second row, for all $`(\tau,z)`$ in a neighbourhood of $`(0,0)`$,


```math
z\ne0,\ f(\tau,z)=0\ \Longrightarrow\ \tau\beta>0\ \text{ and }\ \partial_zf(\tau,z)\,\beta<0.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.branch_side_eventually` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L123): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### At most one small zero of each sign

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the second row there is $`\rho>0`$ such that for all $`\tau`$ in a neighbourhood of $`0`$ and all $`z_1,z_2\in\mathbb R`$,


```math
z_1z_2>0,\ |z_1|\le\rho,\ |z_2|\le\rho,\ f(\tau,z_1)=f(\tau,z_2)=0\ \Longrightarrow\ z_1=z_2.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.small_zero_eq_branch` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L145): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Exchange of stability on the exact cubic

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha,\beta,\tau,A\in\mathbb R`$ with $`\beta\ne0`$, $`A\ne0`$ and $`\alpha\tau A-\beta A^3=0`$. Then


```math
\frac{d}{dA'}\Big(\alpha\tau A'-\beta A'^3\Big)\Big|_{A'=A}=-2\alpha\tau.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.deriv_cubicField_at_branch` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L163): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem deriv_cubicField_at_branch (alpha beta tau A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    deriv (fun A => alpha * tau * A - beta * A ^ 3) A = -2 * alpha * tau
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Square-root amplitude error

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha,\beta,\tau,z,e,C\in\mathbb R`$ with $`\beta\ne0`$, $`z\ne0`$, $`\alpha\tau-\beta z^2+e=0`$, $`\alpha\tau/\beta\ge0`$ and $`|e|\le C|z|^3`$. Then


```math
\Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le\frac{Cz^2}{|\beta|}.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.abs_sub_sqrt_le_of_cubic_remainder` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L174): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem abs_sub_sqrt_le_of_cubic_remainder (alpha beta tau z e C : ℝ)
    (hbeta : beta ≠ 0) (hs : z ≠ 0)
    (hroot : alpha * tau - beta * z ^ 2 + e = 0)
    (ht : 0 ≤ alpha * tau / beta) (herr : |e| ≤ C * |z| ^ 3) :
    |(|z| - Real.sqrt (alpha * tau / beta))| ≤ C * z ^ 2 / |beta|
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Remainder bounds from jets at the origin

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`0<r\le1`$ and let $`R:\mathbb R^2\to\mathbb R`$ be $`C^4`$ on an open set $`U`$ containing the box $`\{|\tau|,|z|\le r\}`$. Assume $`R(\tau,0)=0`$ for $`|\tau|\le r`$ and


```math
\partial_zR=\partial_\tau\partial_zR=\partial_z^2R=\partial_\tau\partial_z^2R=\partial_z^3R=0\quad\text{at }(0,0).
```


Then there is $`C\ge0`$ such that for $`|\tau|,|z|\le r`$: $`|R(\tau,z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)`$, $`R(\tau,\cdot)`$ has derivative $`\partial_zR(\tau,z)`$ at $`z`$, and $`|\partial_zR(\tau,z)|\le C(\tau^2+z^2|\tau|+|z|^3)`$; and $`\tau\mapsto R(\tau,z)`$ is continuous at every $`|\tau|<r`$, $`|z|\le r`$.


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.remainderBounds_of_jet` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L190): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### The stronger remainder bound holds iff the axis condition holds

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the previous row,


```math
\Big(\exists C\ \forall\,|\tau|,|z|\le r:\ |R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big)\Big)\iff \partial_zR(\tau,0)=0\ \text{ for all }|\tau|\le r.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.strongBound_iff_axis` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L213): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### The jets at the origin do not give the stronger bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

It is not true that every $`R`$, $`U`$, $`r`$ satisfying the hypotheses of the row "Remainder bounds from jets at the origin" admit a constant $`C`$ with


```math
|R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big)\quad\text{for all }|\tau|,|z|\le r.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.jet_not_sufficient_for_strongBound` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L231): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### A non-compact component has unbounded parameter

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`E`$ be a topological space and $`C,S,V\subseteq\mathbb R\times E`$ with $`C\subseteq V`$, $`C`$ closed in the subspace $`V`$, $`C\subseteq\overline S\subseteq V`$, and $`\overline{S\cap\{(\lambda,u):\lambda\le X\}}`$ compact for every $`X\in\mathbb R`$. If $`C`$ is not compact, then


```math
\forall M\in\mathbb R\ \exists(\lambda,u)\in C:\ \lambda>M,\qquad \sup\{\lambda:(\lambda,u)\in C\}=+\infty\ \text{ in }\overline{\mathbb R}.
```


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.Global.sSup_param_eq_top` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L255): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem sSup_param_eq_top {E : Type*} [TopologicalSpace E] {C S V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### The one-sided component is closed

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`X`$ be a topological space, $`S\subseteq X`$ closed, $`b\in S`$, and $`K`$ the connected component of $`b`$ in $`S`$. Let $`A\subseteq X`$ with $`A\cap K`$ open in the subspace $`K`$, and let $`s\in K\setminus A`$. Then the connected component of $`s`$ in $`K\setminus A`$ is closed in $`X`$.


**Lean.** `ScalarPitchforkHeadline.ScalarPitchfork.Global.selectedComponent_isClosed` in [ScalarPitchfork/HeadlineChallenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/HeadlineChallenge.lean#L271): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Pitchfork branches under the stronger remainder bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the row "Remainder bounds from jets at the origin" together with the axis condition $`\partial_zR(\tau,0)=0`$ for $`|\tau|\le r`$ (where $`\partial_zR(\tau,z)=DR(\tau,z)(0,1)`$), there is $`C\ge0`$ with, for $`|\tau|,|z|\le r`$,


```math
|R(\tau,z)|\le C\big(z^2\tau^2+|z|^3|\tau|+z^4\big),\qquad |\partial_zR(\tau,z)|\le C\big(|z|\tau^2+z^2|\tau|+|z|^3\big).
```


The axis condition holds for $`R(\tau,z)=f(\tau,z)-\alpha\tau z+\beta z^3`$ when $`R`$ satisfies those jet hypotheses and $`\partial_zf(\tau,0)=\alpha\tau`$ for $`|\tau|\le r`$; and if $`\varphi'(0)=d`$ and $`|\varphi(z)|\le Kz^2`$ for $`|z|\le\delta`$ with $`\delta>0`$, then $`d=0`$.
Let $`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`0<r\le1`$, $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$, and assume for $`|\tau|,|z|\le r`$ the two stronger bounds above with $`\partial_zR=R_z`$. Then the conclusion of the row "Existence of both branches with explicit amplitude constant and stability sign" holds with the same constant $`K`$. If moreover $`\tau\mapsto R(\tau,z)`$ is continuous at every $`|\tau|<r`$, $`|z|\le r`$, there are $`\rho>0`$, an open neighbourhood $`N`$ of $`0`$ and, for $`\sigma\in\{1,-1\}`$, functions $`b_\sigma`$ continuous on $`N`$ with $`b_\sigma(\tau)\to0`$ as $`\tau\to0`$, such that for $`\tau\in N`$ with $`\tau\beta>0`$, $`f(\tau,\cdot)`$ has exactly one zero $`z`$ with $`\sigma z>0`$, $`|z|\le\rho`$, and $`b_\sigma(\tau)`$ is that zero.
At a single point: if $`z\ne0`$, $`|z|,|\tau|\le1`$, $`2C|\tau|\le\alpha`$, $`\alpha\tau z-\beta z^3+R=0`$, $`d=\alpha\tau-3\beta z^2+R_s`$, $`|R|\le C(z^2\tau^2+|z|^3|\tau|+z^4)`$, $`|R_s|\le C(|z|\tau^2+z^2|\tau|+|z|^3)`$ and $`A(|\tau|+|z|)\le|\beta|/2`$ with $`A=C\big(\frac{2(|\beta|+2C)}{\alpha}+1\big)`$, then $`\tau\beta>0`$, $`d\beta<0`$ and $`\big||z|-\sqrt{\alpha\tau/\beta}\big|\le K|\tau|`$.


**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.strongBounds_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L297): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.branch_eventually_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L320): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.branch_curves_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L346): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.equilibrium_core_of_strongBound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L371): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.deriv_zero_of_sq_bound` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L513): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ z, |z| ≤ δ → |φ z| ≤ K * z ^ 2) : d = 0
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.axis_of_linearization` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L392): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Pitchfork branches directly from jets at the origin

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha>0`$, $`\beta\ne0`$, and let $`R`$, $`U`$, $`r`$ satisfy the hypotheses of the row "Remainder bounds from jets at the origin" ($`C^4`$ on an open $`U\supseteq\{|\tau|,|z|\le r\}`$, $`0<r\le1`$, $`R(\tau,0)=0`$ for $`|\tau|\le r`$, and the five listed derivatives vanish at $`(0,0)`$); no remainder constant is assumed. Put $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$. Then the full conclusion of the row "The two pitchfork branches" holds for $`f`$ (with some $`\rho>0`$, open neighbourhood $`N`$ of $`0`$, $`K`$ and $`b_{\pm1}`$), and in addition $`b_\sigma(\tau)\to0`$ as $`\tau\to0`$. Moreover there is $`C\ge0`$ such that the conclusion of the row "Existence of both branches with explicit amplitude constant and stability sign" holds for $`f`$ with the explicit constant $`K`$ computed from this $`C`$.


**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.pitchfork_branch_curves_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L462): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.exists_branch_eventually_of_jet` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L491): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Estimates at a single nontrivial equilibrium

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\alpha>0`$, $`\beta\ne0`$, $`C\ge0`$, $`z\ne0`$, $`|z|\le1`$, $`\alpha\tau z-\beta z^3+R=0`$ and $`d=\alpha\tau-3\beta z^2+R_s`$ (real numbers). If $`|R|\le C(|\tau||z|^3+z^4)`$, $`|R_s|\le C(|\tau|z^2+|z|^3)`$ and $`C(|\tau|+|z|)\le|\beta|/2`$, then


```math
\tau\beta>0,\qquad d\beta<0,\qquad \Big||z|-\sqrt{\alpha\tau/\beta}\Big|\le\frac{2\alpha C\big(\frac{3|\beta|}{2\alpha}+1\big)}{|\beta|^2}|\tau|.
```


If instead $`|\tau|\le1`$, $`2C|\tau|\le\alpha`$, $`|R|\le C(|z|\tau^2+|z|^3|\tau|+z^4)`$, $`|R_s|\le C(\tau^2+z^2|\tau|+|z|^3)`$ and $`A(|\tau|+|z|)\le|\beta|/2`$ with $`A=C\big(\frac{2(|\beta|+2C)}{\alpha}+1\big)`$, the same holds with $`C`$ replaced by $`A`$ in the amplitude constant.
If $`\alpha>0`$, $`\beta\ne0`$, $`A\ne0`$ and $`\alpha\tau A-\beta A^3=0`$, then $`A=\pm\sqrt{\alpha\tau/\beta}`$. Finally, let $`\alpha>0`$, $`\tau\beta>0`$, $`C\ge0`$, let $`R:\mathbb R\to\mathbb R`$ be continuous on $`\big[\sqrt{\alpha\tau/(2\beta)},\sqrt{2\alpha\tau/\beta}\big]`$ with $`|R(z)|\le C(|z|\tau^2+|z|^3|\tau|+z^4)`$ for $`0<z`$, $`z^2\le2\alpha\tau/\beta`$, and $`C\big(|\tau|+2\alpha\tau/\beta+2\alpha\sqrt{2\alpha\tau/\beta}/|\beta|\big)<\alpha/2`$. Then there is $`z>0`$ with $`\alpha\tau/(2\beta)\le z^2\le2\alpha\tau/\beta`$ and $`\alpha\tau z-\beta z^3+R(z)=0`$.


**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.perturbed_equilibrium_core` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L422): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.equilibrium_core` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L442): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.exists_pos_equilibrium` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L533): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.nonzero_equilibrium_eq_branch` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L522): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem nonzero_equilibrium_eq_branch (alpha beta tau A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : alpha * tau * A - beta * A ^ 3 = 0) :
    A = Real.sqrt (alpha * tau / beta) ∨ A = -Real.sqrt (alpha * tau / beta)
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Global alternatives under monotone profiles

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`E`$ be a topological additive group, $`P:E\to(\mathbb R\to\mathbb R)`$ an additive map (the profile), $`L>0`$, $`(\lambda^*,u^*)\in\mathbb R\times E`$, $`W\subseteq E`$ and $`C,S,V\subseteq\mathbb R\times E`$. Assume the global alternatives: $`C`$ is not compact, or $`(\lambda,u^*)\in C`$ for some $`\lambda\ne\lambda^*`$, or $`(\lambda,u^*+w)\in C`$ for some $`w\in W\setminus\{0\}`$. Assume $`P(u^*)`$ is constant, every $`P(e)`$ is continuous on $`[0,L]`$, every $`(\lambda,u)\in C\setminus\{(\lambda^*,u^*)\}`$ has $`P(u)`$ strictly monotone on $`[0,L]`$, and the weight $`\varphi`$ satisfies


```math
\int_0^Lg\,\varphi\,dx>0\ \text{ for every continuous strictly decreasing }g\text{ on }[0,L],\qquad \int_0^LP(w)\,\varphi\,dx=0\ \ (w\in W).
```


Then the second and third alternatives fail; if in addition $`C`$ satisfies the hypotheses of the row "A non-compact component has unbounded parameter" except non-compactness ($`C\subseteq V`$ relatively closed in $`V`$, $`C\subseteq\overline S\subseteq V`$, $`\overline{S\cap\{\lambda\le X\}}`$ compact for all $`X`$), then $`C`$ is not compact, has parameters $`\lambda>M`$ for every $`M`$, and $`\sup\{\lambda:(\lambda,u)\in C\}=+\infty`$.
Supporting facts: the alternatives with the last two excluded give non-compactness; if $`C`$ is closed, $`C\subseteq\overline S`$ and all $`\overline{S\cap\{\lambda\le X\}}`$ are compact, every slice $`C\cap\{\lambda\le X\}`$ is compact; if $`C`$ is preconnected, $`p^*\in C\cap M`$ and $`C\cap M`$ is clopen in $`C`$, then $`C\subseteq M`$; in particular, if $`\{p\in C: p=p^*\text{ or }P(p_2)\text{ is strictly decreasing on }[0,L]\}`$ is clopen in a preconnected $`C\ni p^*`$, every $`p\in C\setminus\{p^*\}`$ has strictly decreasing profile.


**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.global_unbounded_of_monotone` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L561): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_altComplement` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L585): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_altOtherTrivial` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L602): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem not_altOtherTrivial {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {prof : E →+ (ℝ → ℝ)} {L c lamStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hMono : ∀ p ∈ C, p ≠ (lamStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.not_isCompact_of_alternatives` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L614): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem not_isCompact_of_alternatives {E : Type*} [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {lamStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : ¬ IsCompact C ∨ (∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C) ∨
      ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C)
    (hNotII : ¬ ∃ lam : ℝ, lam ≠ lamStar ∧ (lam, uStar) ∈ C)
    (hNotIII : ¬ ∃ lam : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (lam, uStar + w) ∈ C) :
    ¬ IsCompact C
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isCompact_slice` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L626): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem isCompact_slice {E : Type*} [TopologicalSpace E] {C S : Set (ℝ × E)}
    (hClosed : IsClosed C) (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar})
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.subset_of_relClopen` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L636): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem subset_of_relClopen {E : Type*} [TopologicalSpace E] {C M : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C) (hStarM : pStar ∈ M)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' M)) :
    C ⊆ M
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.strictAntiOn_of_relClopen` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L648): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem strictAntiOn_of_relClopen {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹'
      {p | p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)})) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L)
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Closedness and containment of one-sided components

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`X`$ be a topological space. A connected component of a closed set $`F`$ (of a point of $`F`$) is closed, and if $`P`$ is closed and $`A\cap P`$ is open in the subspace $`P`$, then $`P\setminus A`$ is closed. Let $`S\subseteq X`$ be closed, $`b\in S`$ and $`K`$ the connected component of $`b`$ in $`S`$; then $`K`$ is closed, and $`K\setminus A`$ is closed whenever $`A\cap K`$ is open in the subspace $`K`$.
For any $`A,A'\subseteq X`$ and $`s\in X`$, the component $`K_s`$ of $`s`$ in $`K\setminus A`$ satisfies $`K_s\subseteq S`$. If $`\{b\}\cup A'`$ is connected and contained in $`S`$, then $`\{b\}\cup A'\subseteq K`$; if moreover $`\{b\}\cup A'`$ is disjoint from $`A`$, then $`\{b\}\cup A'\subseteq K\setminus A`$, and for every $`s\in A'`$,


```math
\{b\}\cup A'\subseteq K_s,\qquad\text{in particular } b\in K_s.
```


**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isClosed_connectedComponentIn_of_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L662): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X]
    {F : Set X} {x : X} (hF : IsClosed F) (hx : x ∈ F) :
    IsClosed (connectedComponentIn F x)
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.isClosed_sdiff_of_isOpen_preimage` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L670): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem isClosed_sdiff_of_isOpen_preimage {X : Type*} [TopologicalSpace X]
    {parent removed : Set X} (hParent : IsClosed parent)
    (hRemoved : IsOpen (((↑) : parent → X) ⁻¹' removed)) :
    IsClosed (parent \ removed)
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.parentComponent_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L680): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem parentComponent_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure) :
    IsClosed (connectedComponentIn solutionClosure base)
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.unilateralRemainder_isClosed` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L690): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem unilateralRemainder_isClosed {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen (((↑) : connectedComponentIn solutionClosure base → X) ⁻¹' removedArc)) :
    IsClosed (connectedComponentIn solutionClosure base \ removedArc)
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_parentComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L702): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem retainedWithBase_subset_parentComponent {X : Type*} [TopologicalSpace X]
    {solutionClosure retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_unilateralRemainder` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L714): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem retainedWithBase_subset_unilateralRemainder {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆ connectedComponentIn solutionClosure base \ removedArc
```

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.retainedWithBase_subset_selectedComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L727): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.base_mem_selectedComponent` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L742): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `ScalarPitchforkAudit.ScalarPitchfork.Global.selectedComponent_subset_solutionClosure` in [ScalarPitchfork/Challenge.lean](https://github.com/chenle02/scalar-pitchfork-lean/blob/a460cf60cfe88aa90019be59d45a1d0f14ece7e7/ScalarPitchfork/Challenge.lean#L756): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem selectedComponent_subset_solutionClosure {X : Type*} [TopologicalSpace X]
    {solutionClosure removedArc : Set X} {base selector : X} :
    connectedComponentIn (connectedComponentIn solutionClosure base \ removedArc) selector ⊆
      solutionClosure
```

</details>


Every result with each of its claims, in one table: [Coverage](coverage.md).


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `a460cf60cfe88aa90019be59d45a1d0f14ece7e7` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

## Not proved here

- No Crandall–Rabinowitz theorem and no center-manifold reduction: the scalar normal form $`\alpha\tau z-\beta z^3+R`$ is the starting point, not derived from an operator equation.
- No Lyapunov–Schmidt reduction.
- No degree theory: no Leray–Schauder degree and no Rabinowitz global alternative. The global part is the topological skeleton only; the alternatives are hypotheses, not derived from degree theory.
- No certified-root tools: no interval arithmetic or root isolation for specific polynomials.
- No PDE: no existence, uniqueness or regularity theorem for any differential equation.

The newer paper companion has its own source and evidence. Its additions are not automatically
part of this standalone library, and neither library establishes whole-paper verification.

<details>
<summary>Lean implementation notes</summary>

The Lean statement, including every binder and hypothesis, controls the result. Definitions may be
total outside their mathematical domain; apply results only under their explicit domain assumptions.
The folded blocks are trusted Challenge statements checked against separate Solution proofs.

</details>

## How this was checked

The [generated verification page](verification.md) and [coverage ledger](coverage.md) retain the
full receipt table and exact declaration mappings. This documentation update changes no Lean source,
claims, toolchain or dependency pins and runs no new proof gate. It does not expand the comparator's
configured scope. See [formalization metadata](../formalization.yaml) for recorded review status.

## References and reuse

- [Paper and bibliographic references](../README.md#paper-and-references), including the BibTeX entry.
- [Software citation](../CITATION.cff) and [license](../LICENSE).
- [Paper III source](https://github.com/chenle02/chemotaxis-paper-iii).
- [Paper III Lean companion](https://github.com/chenle02/chemotaxis-paper-iii-lean).
