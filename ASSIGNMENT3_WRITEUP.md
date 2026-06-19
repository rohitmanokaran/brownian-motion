# Formalizing a proof of Itô's formula in Lean

## Executive summary

This project was an AI-assisted contribution to the
[RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion)
Lean repository. The repository formalizes Brownian motion and is building
the stochastic-calculus infrastructure needed for results such as Itô's
formula. The original project goal was ambitious: prove the Brownian quadratic
variation theorem

```lean
ProbabilityTheory.quadraticVariation_brownian
```

and the upstream dependency chain needed for a proof of Itô's formula. During
the project, this turned out to be too large for the course window. The theorem
depends on optional sampling, local martingales, square integrability,
predictable quadratic variation, Doob-Meyer decomposition, and finite-variation
uniqueness infrastructure. Several of those pieces still contain upstream
`sorry`s or require substantial API design work.

The final project therefore became a smaller but more useful upstreaming task:
extract AI-generated work into small, reviewable pull requests that close real
dependency-graph items or improve the API needed for quadratic variation. The
submitted PRs are:

| PR | Status on June 19, 2026 | Contribution |
| --- | --- | --- |
| [#468](https://github.com/RemyDegenne/brownian-motion/pull/468) | Merged | Proved scalar multiplication preserves square-integrable martingales. |
| [#471](https://github.com/RemyDegenne/brownian-motion/pull/471) | Merged | Added càdlàg composition and norm-square helpers, closing a quadratic-variation càdlàg placeholder. |
| [#473](https://github.com/RemyDegenne/brownian-motion/pull/473) | Open, CI passing | Defines locally square-integrable martingales, adds a global-to-local bridge, and proves their squared norm is a local submartingale. |
| [#469](https://github.com/RemyDegenne/brownian-motion/pull/469) | Open, CI passing | Changes `quadraticVariation` to require local square-integrability, the mathematically necessary hypothesis for the Doob-Meyer construction. |

There is also a larger exploratory draft,
[#463](https://github.com/RemyDegenne/brownian-motion/pull/463), containing a
snapshot of Brownian quadratic-variation work. That branch is not suitable as a
final PR because it mixes many unrelated generic and Brownian-specific changes.

## Why Itô's formula was the target

Itô's formula is the stochastic analogue of the chain rule. For a sufficiently
smooth function `f` and a Brownian motion `B`, the one-dimensional form is

```text
f(B_t) = f(B_0) + ∫_0^t f'(B_s) dB_s + 1/2 ∫_0^t f''(B_s) ds.
```

The extra second-order term is the key stochastic phenomenon. It appears because
Brownian paths have nonzero quadratic variation:

```text
<B>_t = t.
```

This is also why Itô's formula is central in finance. Black-Scholes style
models describe asset prices using stochastic differential equations. Their
pricing equations come from applying Itô's formula to functions of stochastic
processes. So a machine-checked derivation of Itô's formula is not just a
formalization exercise; it is a formal foundation for a major applied
mathematical tool.

## Possible proof routes in Lean

There are several levels at which one can formalize Itô's formula. They differ
mainly in how much reusable stochastic calculus infrastructure they require.

### 1. Analytic or discrete-approximation proof

The most direct route is to prove Itô's formula for Brownian motion by working
with partitions and Taylor expansion:

```text
f(X_{t_{i+1}}) - f(X_{t_i})
```

is expanded and summed over a partition. One then proves convergence of the
first-order term to the stochastic integral and convergence of the second-order
Brownian term using

```text
Σ (ΔB_i)^2 -> t.
```

This route is probably the easiest to make work in Lean for a first proof
because it avoids building the full general theory of semimartingales. The
draft paper *From Itô to Black-Scholes: A Machine-verified Derivation in Lean 4*
uses this kind of direct analytic strategy.

The disadvantage is that the result is less reusable. It gives a proof of a
particular theorem, but not the general stochastic-calculus API that later
results need.

### 2. Quadratic-variation proof

The next route is to first prove Brownian quadratic variation:

```text
<B>_t = t.
```

Then Itô's formula follows from a theorem whose second-order term is written in
terms of quadratic variation. This route is more mathematically structural. It
requires formal definitions of quadratic variation, stochastic integration,
local martingales, and square-integrability hypotheses.

This was the route I targeted first. The reasoning was that
`quadraticVariation_brownian` is a concrete dependency on the path to Itô's
formula, and the repository's blueprint already contains the intended theorem.

### 3. Continuous-local-martingale proof

A more reusable theorem proves Itô's formula for continuous local martingales.
This is much more powerful than a Brownian-only theorem. It covers Brownian
motion, stochastic integrals, time-changed Brownian motion, the
Dambis-Dubins-Schwarz theorem, and many SDE examples.

This route needs a larger API:

- stopping times;
- localization;
- local martingales;
- predictable quadratic variation;
- square integrability;
- stochastic integrals.

This is closer to the direction of the Brownian-motion project, but it is too
large to finish in a short assignment without already having most of the
infrastructure.

### 4. Semimartingale proof

The textbook endpoint is a semimartingale theorem. A continuous semimartingale
has the form

```text
X = M + A,
```

where `M` is a continuous local martingale and `A` is a finite-variation
adapted process. The full càdlàg semimartingale theorem also includes jumps.

This is the most reusable statement: Brownian Itô becomes a corollary instead
of a special theorem. But it also requires semimartingales, finite variation,
covariation, predictable quadratic variation, and a mature stochastic-integral
framework. This repository is moving in that direction.

The Brownian-motion blueprint defines predictable quadratic variation using the
Doob-Meyer decomposition: for a suitable martingale `M`, `⟨M⟩` is the
predictable part of the Doob-Meyer decomposition of `‖M‖^2`. This is a serious
textbook-style construction. It is also the reason the proof path has many
upstream dependencies.

## Starting point: the dependency graph

The repository has a blueprint and dependency graph:

https://remydegenne.github.io/brownian-motion/blueprint/dep_graph_document.html

The graph is useful, but it is not a complete implementation plan. Some nodes
were marked with Lean statements that did not yet have mathematically adequate
hypotheses. Other nodes depended on large generic tools that were only partly
proved. In particular, the path to `quadraticVariation_brownian` involved:

- measure-theoretic foundations;
- filtrations and stopping times;
- optional sampling;
- local martingales and local submartingales;
- square-integrable martingales;
- Doob-Meyer decomposition;
- predictable finite-variation uniqueness;
- quadratic variation;
- Brownian-specific martingale and square-integrability facts.

After exploring the graph and the Archon history, my estimate is that a complete
high-quality proof of Brownian Itô via the general semimartingale route is still
on the order of one to two years of expert Lean work, even with LLM assistance.
This is not because any one theorem is conceptually impossible, but because the
number of intermediate APIs, stability lemmas, and review-quality proofs is
large.

## Target selection

I initially used the LLM as a planning assistant. The prompt was essentially:

> What is the smallest target on the path to Itô's formula that has a useful
> mathematical statement, fits the existing blueprint, and could plausibly be
> completed by an agentic coding assistant?

The suggested target was Brownian quadratic variation:

```lean
ProbabilityTheory.quadraticVariation_brownian
```

Mathematically, the theorem says that if `B` is standard Brownian motion, then
the quadratic variation process is deterministic:

```text
<B>_t = t.
```

The intended proof through the repository's API is:

1. Show `B_t^2 - t` is a martingale.
2. Show the deterministic process `t` is predictable, càdlàg, increasing, and
   normalized at zero.
3. Use Doob-Meyer uniqueness to identify the predictable part of `B_t^2` with
   `t`.
4. Conclude that the quadratic variation selected by `quadraticVariation` is
   `t`.

This is a clean mathematical plan. The problem is that the generic theorem stack
under step 3 was not fully available.

## Attempt 1: follow the blueprint rigidly

The first serious attempt was to run Archon and Codex with instructions not to
change the dependency-graph APIs. The idea was to keep the agent honest: close
the existing `sorry`s, do not invent a new theorem hierarchy, and do not bypass
the blueprint.

This failed after several days of iteration. The agent generated thousands of
lines of helper lemmas, especially around Doob-Meyer uniqueness and optional
sampling. Some helpers were real progress, but the branch became too large and
too hard to review. Worse, the agent started churning: each run produced more
infrastructure without closing the final theorem.

The important lesson was that the blueprint API was not perfectly aligned with
the mathematics. The most important example was the square-norm local
submartingale theorem.

The existing public theorem was morally:

```lean
IsLocalMartingale X -> cadlag X -> IsLocalSubmartingale (fun t ω => ‖X t ω‖ ^ 2)
```

But the proof of `‖X‖^2` being a submartingale needs second moments. The
repository's own theorem

```lean
IsSquareIntegrable.submartingale_sq_norm
```

requires square integrability. A generic local martingale does not supply the
needed `L^2` hypotheses. So the blueprint node had to be redesigned instead of
proved as written.

## Attempt 2: ignore the blueprint route

The second attempt relaxed the constraint and let the AI try a more direct
finite-variation or discrete-approximation approach. This was closer to the
analytic proof route discussed above.

That also failed as an upstream contribution. It could produce plausible local
code, but it did not fit the repository's design. The repository is building
general stochastic-calculus infrastructure, not just a one-off Brownian
calculation. A direct Brownian-specific proof would bypass the dependency graph
instead of advancing it.

This attempt clarified the project requirement: the goal was not merely to get
Lean to accept some theorem statement. The goal was to move the upstream project
forward in a form maintainers could review and eventually merge.

## Attempt 3: split into small upstream PRs

The successful strategy was to stop trying to submit the whole Brownian
quadratic-variation branch. Instead, I treated the AI-generated snapshot as a
source of possible reviewable lemmas. Each candidate was checked against three
questions:

1. Does it close an existing `sorry` or implement a real blueprint dependency?
2. Is it mathematically honest, with the right hypotheses?
3. Is the diff small and readable enough for upstream review?

This produced several focused PRs.

### PR #468: scalar multiplication of square-integrable martingales

PR #468 proves:

```lean
IsSquareIntegrable.smul
```

This says that if `X` is a square-integrable martingale and `r : ℝ`, then
`r • X` is also square-integrable.

The first Codex-generated proof compiled but was not very readable. It used a
rough `refine ⟨?_, ?_, ?_⟩` proof and a somewhat dense `calc` block. A web
ChatGPT Pro model suggested a cleaner structure-style proof, and then local
Codex adapted that proof until Lean accepted it. This was a concrete example of
using one model for mathematical/readability review and another for local
repository execution.

The PR was merged on June 17, 2026.

### PR #471: càdlàg norm-square helper

PR #471 was split out of the larger quadratic-variation PR. It added reusable
càdlàg composition infrastructure, including a helper showing that if `X` has
càdlàg paths, then `t ↦ ‖X_t‖^2` has càdlàg paths.

This directly closed the local `hX2_cadlag` placeholder in
`QuadraticVariation.lean`:

```lean
have hX2_cadlag : ∀ ω, IsCadlag (fun t => ‖X t ω‖ ^ 2) :=
  fun ω => IsCadlag.norm_sq (hX_cadlag ω)
```

The split was valuable because it let reviewers evaluate a small general helper
without also reviewing the quadratic-variation API change. The PR was merged on
June 19, 2026.

### PR #473: locally square-integrable martingales

PR #473 introduces the API that the quadratic-variation construction actually
needs:

```lean
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y => IsSquareIntegrable Y 𝓕 P) 𝓕 X P
```

It also adds the global-to-local bridge:

```lean
lemma IsSquareIntegrable.isLocallySquareIntegrable
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX
```

and the key theorem:

```lean
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm
    (hX : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω => ‖X t ω‖ ^ 2) 𝓕 P
```

This is the mathematically honest replacement for the earlier bare
local-martingale theorem. It says that a locally square-integrable martingale
has a squared norm that is a local submartingale.

As of June 19, 2026, this PR is open and its GitHub build is passing.

### PR #469: local square-integrability in quadratic variation

PR #469 changes `quadraticVariation` to use the stronger hypothesis from PR
#473. The intended API is:

```lean
def quadraticVariation
    (hX_sq : IsLocallySquareIntegrable X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ
```

The separate càdlàg argument remains because the current `predictablePart` API
requires paths to be càdlàg for every `ω`. Local square-integrability provides
càdlàg paths for localized stopped processes, but it does not directly match
that global pathwise argument requirement.

This PR is deliberately dependent on #473. After #473 merges, #469 can be
rebased so its visible diff contains only the quadratic-variation API change.
As of June 19, 2026, this PR is open and its GitHub build is passing.

## Other explored work

The larger draft PR #463, "Advance Brownian quadratic variation", contains much
more code from the exploratory branch. It includes Brownian-specific helpers and
generic Doob-Meyer/quadratic-variation work. It is still a draft because it is
too large and mixes too many concerns.

PR #465 attempted bounded natural-time optional sampling. That work became less
useful as a standalone submission because upstream PR #450 merged first and
closed the relevant target. This is a good example of why small PRs matter:
large agent-generated branches can become obsolete before review.

PR #461, "Prove exists_modification_left_right_limit", is related to Doob
regularization and was submitted separately by the professor. It illustrates
the size of this dependency chain: a single serious regularization statement
can require a very large proof.

## How I drove the AI systems

I used three kinds of AI assistance.

First, I used local Codex as the main engineering agent. It explored the Lean
repository, searched for relevant APIs, edited files, ran `lake build`, managed
branches, and prepared PRs. This was the agent used for most concrete Lean and
Git work.

Second, I used Archon for longer proof-search loops. Archon was useful for
finding possible proof routes and exposing which obligations were blocking the
dependency chain. Its history reached many iterations and recorded useful
facts, such as:

- the Brownian local square-integrability supplier was axiom-clean;
- the deterministic-time running-supremum facts were axiom-clean;
- the fixed-time Brownian quadratic-variation theorem was still transitively
  tainted by generic dependencies;
- optional sampling and predictable finite-variation uniqueness remained major
  blockers.

Third, I used ChatGPT Pro for higher-level mathematical and style review. This
was especially helpful when local Codex produced compiling but rough Lean code.
For example, in PR #468, the web model suggested a more idiomatic structure
proof, which local Codex then adapted and verified.

The most effective prompts were not "prove this theorem". The effective prompts
were more constrained:

- identify the smallest useful PR;
- remove unused helpers;
- keep only functions on the dependency path;
- follow mathlib style;
- avoid unrelated blueprint or documentation churn;
- explain why an API hypothesis is mathematically necessary;
- split a large PR into smaller reviewable units.

## What went wrong

The main failure mode was overgeneration. When the LLM was asked to solve the
large target directly, it generated many helper lemmas. Some were correct and
useful, but the branch became unreviewable. The agent was optimizing for
"eventually make Lean accept the target", not for "produce a small upstream PR".

The second failure mode was excessive rigidity. When instructed not to change
the dependency graph APIs, the agent tried to prove statements whose hypotheses
were mathematically too weak. The squared-norm local-submartingale theorem was
the clearest example. A bare local martingale is not enough; local square
integrability is needed.

The third failure mode was route mismatch. When the agent was allowed to ignore
the blueprint, it could move toward direct Brownian-specific or finite-variation
arguments. Those may be easier for Lean, but they do not advance the repository
toward its general stochastic-calculus endpoint.

## What worked

The workflow that worked was:

1. Let the AI explore a large proof space.
2. Treat the resulting branch as a mine of possible lemmas, not as a PR.
3. Identify the smallest mathematically meaningful unit.
4. Move that unit to the correct file.
5. Delete unused helpers.
6. Reduce the diff.
7. Write a concise PR description.
8. Iterate on reviewer-style objections before asking for review.

This produced real merged contributions (#468 and #471) and two open,
build-passing PRs (#473 and #469).

## Remaining work

The next steps are:

1. Get #473 reviewed and merged.
2. Rebase #469 on upstream `master` after #473 merges, so it contains only the
   quadratic-variation API change.
3. Continue splitting #463 into smaller PRs, but only when each PR closes a real
   dependency or blueprint node.
4. Resume work on the generic blockers: optional sampling, local submartingale
   stability, Doob-Meyer predictable-part uniqueness, and finite-variation
   uniqueness.
5. Once the generic route is clean, return to `quadraticVariation_brownian`.

The Brownian theorem itself is not the only hard part. The real work is making
the generic stochastic-calculus infrastructure strong enough that the Brownian
theorem becomes a corollary.

## Lessons learned

My main lesson is that LLMs can produce Lean code faster than humans can review
it. That is powerful, but it changes the bottleneck. The hardest part was not
asking the model to write code; it was communicating the right constraints:

- do not bypass the dependency graph with a special-case proof;
- do not follow the dependency graph so rigidly that mathematically wrong APIs
  are preserved;
- do not submit a giant generated branch;
- make the proof readable enough for maintainers;
- split work into conceptual units that can be reviewed.

The most valuable future tool would be an agent that specializes in upstreaming:
given a large AI-generated proof branch, it would identify small PR boundaries,
remove unused helpers, detect API churn, write concise PR descriptions, and
predict reviewer objections. Building that agent was too large for this course,
but this project made clear why it would be useful.

## References

- Project repository:
  https://github.com/rohitmanokaran/brownian-motion
- Upstream repository:
  https://github.com/RemyDegenne/brownian-motion
- Blueprint dependency graph:
  https://remydegenne.github.io/brownian-motion/blueprint/dep_graph_document.html
- *Formalization of Brownian motion in Lean*:
  https://arxiv.org/abs/2511.20118
- Draft *From Itô to Black-Scholes: A Machine-verified Derivation in Lean 4*:
  https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503
- Submitted PRs:
  [#468](https://github.com/RemyDegenne/brownian-motion/pull/468),
  [#471](https://github.com/RemyDegenne/brownian-motion/pull/471),
  [#473](https://github.com/RemyDegenne/brownian-motion/pull/473),
  [#469](https://github.com/RemyDegenne/brownian-motion/pull/469)
