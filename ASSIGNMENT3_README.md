# Assignment 3: AI-assisted Lean formalization in Brownian motion

Repository: https://github.com/rohitmanokaran/brownian-motion

Upstream project: https://github.com/RemyDegenne/brownian-motion

## Project

This project contributes to the Lean formalization of Brownian motion and
stochastic integration. The original goal was to prove the Brownian quadratic
variation theorem

```lean
ProbabilityTheory.quadraticVariation_brownian
```

together with the upstream dependency chain needed for that theorem. That target
turned out to be too large for the assignment window: the proof depends on
generic optional-sampling infrastructure, local submartingale stability,
square-integrable convergence, predictable finite-variation uniqueness, and
Doob-Meyer infrastructure that still contains unresolved `sorry`s upstream.

The final scoped project was therefore to extract reviewable upstream PRs from
the larger AI-generated proof attempt.

## Submitted PRs

| PR | Status | Description |
| --- | --- | --- |
| [#468](https://github.com/RemyDegenne/brownian-motion/pull/468) | Merged | Proves `IsSquareIntegrable.smul`: scalar multiplication preserves square-integrable martingales. |
| [#471](https://github.com/RemyDegenne/brownian-motion/pull/471) | Merged | Adds càdlàg composition and norm-square helpers, and closes the squared-norm càdlàg proof in `quadraticVariation`. |
| [#469](https://github.com/RemyDegenne/brownian-motion/pull/469) | Open | Proves the generic quadratic-variation placeholders under the mathematically necessary local square-integrability hypothesis. |

For PR #468, a local Codex agent first produced compiling but rough Lean code. A
web ChatGPT Pro model then suggested a more readable structure-style proof,
which was adapted locally and accepted by Lean.

PR #471 was split from PR #469 to keep the càdlàg helper change reviewable on
its own. PR #469 now contains the remaining API change: it requires local
square-integrability instead of using a statement that only assumed a cadlag
local martingale before applying Doob-Meyer to `‖X‖^2`.

## Larger exploratory work

The larger draft PR [#463](https://github.com/RemyDegenne/brownian-motion/pull/463)
contains the Brownian quadratic-variation snapshot. It is still too large for
review because it mixes Brownian-specific work with generic Doob-Meyer and
quadratic-variation API changes.

Other explored branches were not submitted as final outputs:

- [#465](https://github.com/RemyDegenne/brownian-motion/pull/465) attempted a
  bounded natural-time optional-sampling proof, but upstream
  [#450](https://github.com/RemyDegenne/brownian-motion/pull/450) closed that
  target first.
- [#464](https://github.com/RemyDegenne/brownian-motion/pull/464) was a cadlag
  modification extraction, but it overlapped with
  [#461](https://github.com/RemyDegenne/brownian-motion/pull/461), which was
  submitted separately by the professor.

## AI systems used

- Codex CLI / local Codex for repo exploration, Lean proof attempts, branch
  management, and PR preparation.
- Archon for iterative proof-search loops and dependency-chain exploration.
- ChatGPT Pro / web model for higher-level mathematical API review and
  readability suggestions.

## What I learned

The main lesson was that AI agents can generate a lot of Lean code quickly, but
upstream-quality formalization requires aggressive scoping. The full Brownian
quadratic-variation theorem was reachable only after many generic dependencies,
and several agent-produced branches mixed too many concerns into one PR. The
more successful workflow was to identify a small true dependency, isolate it,
make the proof readable, and submit that as a focused PR.

The final submitted work is therefore not the complete Brownian quadratic
variation theorem, but a set of reviewable steps toward the generic
quadratic-variation dependency chain.
