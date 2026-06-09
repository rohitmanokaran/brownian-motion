# Analogy: continuous FV-martingale uniqueness bridge — is it in Mathlib, and is general-κ idiomatic?

## Mode
api-alignment

## Slug
fv-uniqueness

## Iteration
062

## Question

(1) Does Mathlib already have "a continuous (local) martingale of finite variation is a.e.
constant", or directly composable pieces (zero quadratic variation of continuous FV processes;
continuous local martingale with zero QV is constant)? (2) Is the project's generality — arbitrary
conditionally-complete linearly-ordered `κ` with `WithTop`, `leastGT`, deterministic mesh/partition
hypotheses, and dense / bottom-immediate / left-isolated branch disjunctions — idiomatic for
Mathlib's martingale / FV / QV API, or is it re-deriving analysis Mathlib gives for real time?
Quantify the cost.

## Project artifact(s)
- `BrownianMotion/StochasticIntegral/DoobMeyer.lean:3489` —
  `Martingale.eq_zero_of_predictable_finiteVariation_bounded_continuous_reduction`, the open core
  `sorry` (line 3525). 128 lemmas/theorems, ~3928 lines; ~60 helpers feed this one.
- `BrownianMotion/StochasticIntegral/DoobMeyer.lean:3658` —
  `Martingale.eq_zero_of_predictable_finiteVariation_discrete`, the ℕ case, built on Mathlib's
  `Martingale.eq_zero_of_predictable'`.
- `BrownianMotion/StochasticIntegral/QuadraticVariation.lean:99` — `quadraticVariation` defined as
  the predictable part of the Doob–Meyer decomposition of the squared norm (consumer of the bridge).
- `BrownianMotion/StochasticIntegral/QuadraticVariationBrownian.lean:24` — final consumer,
  instantiates `κ := ℝ≥0`.

## Decisions identified

### Decision: Is the core FV-uniqueness fact (or composable QV pieces) available in Mathlib?

- **Mathlib idiom**: There is none. Exhaustive probe of `.lake/packages/mathlib`:
  - No quadratic variation in probability (only algebraic quadratic forms). `grep -rli quadratic
    Mathlib/Probability` → empty.
  - No continuous-time Doob–Meyer. The only decomposition is the **discrete** Doob decomposition
    `MeasureTheory.predictablePart` / `martingalePart` (`Mathlib/Probability/Martingale/Centering.lean`,
    ℕ-indexed only).
  - No stochastic integral / Itô / Brownian motion / Wiener measure anywhere in Mathlib (the project
    builds Brownian itself).
  - No "continuous local martingale of FV is constant", no "continuous FV ⇒ zero QV", no L²
    orthogonality-of-martingale-increments lemma.
  - The discrete uniqueness fact `Martingale.eq_zero_of_predictable'`
    (`Mathlib/Probability/Martingale/Basic.lean:529`) **is** present and the project already uses it
    in `eq_zero_of_predictable_finiteVariation_discrete`. It is the ℕ-only shadow of the needed fact.
- **Project's current path**: hand-builds the continuous-time fact via a deterministic-partition
  L² square-increment argument (`integral_sq_terminal_eq_*`) + localization
  (`eq_zero_of_localizingSequence_*`). This is mathematically the standard QV-style proof
  (E[M_t²] = E[Σ(ΔM)²] ≤ E[sup|ΔM|·TotVar] → 0).
- **Gap**: divergent-and-required — there is no Mathlib result to align to.
- **Cost of divergence**: none avoidable here; the result genuinely does not exist upstream.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. The chain is **not** a parallel API to an existing Mathlib
  theorem. The route (deterministic-partition square-increment) is the correct math; there is no
  shorter Mathlib idiom because the QV machinery it would compose with does not exist.

### Decision: Generality of the *foundational* process layer (filtration / stopping / predictable / variation) over general κ

- **Mathlib idiom**: Mathlib's process foundations are themselves general over the order index:
  `Filtration`, `IsStoppingTime`, `stoppedProcess` (`Mathlib/Probability/Process/Stopping.lean:64`,
  `Preorder ι`), `IsStronglyPredictable` (`Process/Predictable.lean`), `hitting`/`hittingBtwn`/
  `hittingAfter` (`Process/HittingTime.lean:48,108,499`, up to `ConditionallyCompleteLinearOrderBot
  ι` + `WellFoundedLT`), and `eVariationOn` / `BoundedVariationOn` / `LocallyBoundedVariationOn`
  (`Mathlib/Topology/EMetricSpace/BoundedVariation.lean:55`, `LinearOrder α`).
- **Project's current path**: builds these pieces over `ConditionallyCompleteLinearOrderBot κ` etc.
- **Gap**: identical / aligned. Building the foundations over general κ matches Mathlib's own
  generality. (Minor: `leastGT` is project-local and overlaps the role of Mathlib's
  `hittingAfter`/`hittingBtwn` — a small candidate parallel API, but not load-bearing for the sorry.)
- **Verdict**: DIVERGE_INTENTIONALLY (i.e. the general-κ foundations are fine).

### Decision: Generality of the *analytic core* (partitions / mesh / dominated convergence / order-branch disjunctions) over general κ vs. specialize to ℝ≥0

- **Mathlib idiom**: Mathlib provides no QV/continuous-martingale analysis at *any* index, so this
  must be built. But the analysis it requires is off-the-shelf **for ℝ / ℝ≥0**: Heine–Cantor uniform
  continuity on compact intervals (`Mathlib/Topology/UniformSpace/HeineCantor.lean`), dyadic
  partitions with mesh → 0, dominated convergence, and dense order (`ℝ≥0` is `DenselyOrdered`,
  `Mathlib/Data/NNReal/Defs.lean:84,397`).
- **Project's current path**: re-derives the analysis over general κ with explicit mesh hypotheses
  (`hmesh : ∀ W ∈ 𝓤 κ, ...`) hand-threaded everywhere, and a three-way order-topology branch
  disjunction (dense-left / bottom-immediate / left-isolated).
- **Gap**: divergent-with-cost. The **only** consumer is Brownian over `κ = ℝ≥0`
  (`QuadraticVariationBrownian.lean:24`), which is densely ordered — so the bottom-immediate and
  left-isolated branches are **vacuous for the real target**. Concretely in `DoobMeyer.lean`:
  ~28 declarations carry branch bookkeeping
  (`left_branch`/`dense_left`/`left_isolated`/`bottom_immediate`/`strictPast`/`neBot_left`/
  `of_previous`); ~58 `Or.inl`/`Or.inr`/`hleft` branch-plumbing sites; ~163
  mesh/partition/localizingSequence/modulus/pre_stop references. Most of the branch machinery is
  dead weight at ℝ≥0, and the explicit-mesh threading replaces dyadic refinements that ℝ supplies
  for free.
- **Cost of divergence**: the generality the project pays for is used by zero consumers; it inflates
  the proof with left-isolated/bottom-immediate order analysis that ℝ≥0 makes trivial and forces
  manual mesh bookkeeping where ℝ gives canonical dyadic partitions. This is the likely reason ~60
  helpers accreted without closing the sorry.
- **Verdict**: ALIGN_WITH_MATHLIB (specialize). Prove the core at `κ = ℝ≥0` (or `[0,t] ⊆ ℝ`); keep
  the general-κ statement only as an optional outer wrapper if any future consumer needs it.

## Recommendation

Stop adding general-κ helpers (do **not** write the planned `leastGT` pre-stop / stop-value bound).
The core fact is genuinely absent from Mathlib (NEEDS_MATHLIB_GAP_FILL), so the route must be
built — but it should be built where the analysis is cheap. Since the sole consumer is Brownian over
`ℝ≥0` (densely ordered), close `eq_zero_of_predictable_finiteVariation_bounded_continuous_reduction`
(and its `eq_zero_of_bounded_continuous_finiteVariation_core` premise) **specialized to ℝ≥0** — there
the dense branch is the only one, Heine–Cantor + dyadic partitions are off-the-shelf, and the
~28-declaration / ~58-site branch-disjunction layer and the bespoke mesh threading collapse. The
mathematics of the existing route (deterministic-partition square-increment, L² orthogonality) is
correct and is the standard QV argument; only the index generality, not the proof idea, is the tax.
Re-export to general κ afterward only if a real second consumer appears.
