# Contributing to ScalarPitchfork

Thank you for your interest. Small, explicit interfaces make the library easy to reuse.

## Before you start

- Read README.md, AGENTS.md and the Lean declarations you will touch.
- Use the pinned Lean toolchain and Mathlib manifest together. Run `lake exe cache get`, then `lake build`.
- Open an issue first for a new module or a change of scope.

## A good change

- States the mathematics in one or two sentences, with all hypotheses.
- Compiles locally with no `sorry` and only the standard axioms (`propext`, `Quot.sound`,
  `Classical.choice`).
- Follows Mathlib naming and style. Proofs should be readable, not only correct.
- Adds a short module docstring for a new file and a docstring for each main theorem.
- Updates `claims.yaml`, the comparator configurations, the README headline list and `coverage.yaml` when a
  public result changes.
- Keeps every hypothesis, including `0 < alpha`, `beta ≠ 0`, `0 < r ≤ 1`, the side condition
  `0 < tau * beta` and the smallness of the parameter.

## Provenance and license

All contributions are under Apache-2.0. Keep the copyright headers and the NOTICE file. If you adapt code
from another project, say so in the file header and check that its license allows it. Say clearly when a
result is a known theorem; this library formalizes classical bifurcation theory.

## Good first projects

- Upstreaming to Mathlib the unique-root lemma (intermediate value theorem plus strict monotonicity gives
  `ExistsUnique`) used for the branches.
- A Whyburn-type separation lemma for compact Hausdorff spaces, which the global part takes as a hypothesis.
- The transcritical and saddle-node normal forms in the same quantitative style.
- A Lyapunov–Schmidt reduction that produces the scalar normal form from an operator equation.
