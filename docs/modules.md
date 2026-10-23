---
title: "Modules"
description: "The Lean modules of scalar-pitchfork-lean and what each contains."
---

# Modules

The library root imports every module below.

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
