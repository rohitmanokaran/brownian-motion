/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.ApproxSeq
public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Martingale

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {n : ι}

theorem condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator
    (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ :=
    Integrable.indicator
      (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
      <| hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact (measurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
        hτ).stronglyMeasurable.indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

theorem stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  refine
    (h.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ
      (hσ.min hτ) (fun x ↦ min_le_right _ _) hτ_le hτ_countable_range ?_).trans ?_
  · exact (hτ_countable_range.union hσ_countable_range).mono <| by grind
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices μ[stoppedValue X τ|(hσ.min hτ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stoppedValue X τ|hσ.measurableSpace] by
      rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue X τ
    · rw [IsStoppingTime.measurableSpace_min hσ hτ,
        IsStoppingTime.measurableSpace_min hτ hσ, inf_comm]
    · have h1 : μ[stoppedValue X τ|hτ.measurableSpace] = stoppedValue X τ := by
        apply condExp_of_stronglyMeasurable hτ.measurableSpace_le
        · exact Measurable.stronglyMeasurable <|
            measurable_stoppedValue (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
            hτ
        · exact h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range
      rw [h1]
      exact (h.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range hRC hτ_le
        hτ hσ hτ_countable_range).symm

/-- **Optional sampling theorem** for general time indices
(assuming existence of `DiscreteApproxSequence`). -/
theorem stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  set τn' := (discreteApproxSequence_of 𝓕 hτ_le τn).inf σn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ]
      μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace] := by
    refine EventuallyEq.trans (Eq.eventuallyEq ?_)
      (h.stoppedValue_min_ae_eq_condExp_of_countable_range hRC
        ((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m)
        (σn.isStoppingTime m) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ _) (σn.countable m))
    congr 1; ext ω; rw [min_comm]; rfl
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn
  refine ae_eq_condExp_of_forall_setIntegral_eq _ hintgbl ?_ ?_
    ((measurable_stoppedValue (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
      (hτ.min hσ)).mono ((hτ.min hσ).measurableSpace_mono hσ <| fun ω ↦ min_le_right _ _)
      le_rfl).aestronglyMeasurable
  · exact fun s hs _ ↦ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
      (fun _ ↦ min_le_of_left_le <| hτ_le _) <| τn.inf σn).integrableOn
  rintro s hs -
  have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) =
    fun m ↦ ∫ ω in s, stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) ω ∂μ := by
    ext m
    rw [setIntegral_congr_ae (g := μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace]) (hσ.measurableSpace_le _ hs)
        (by filter_upwards [hint m] with ω hω _ using hω)]
    exact setIntegral_condExp _
      (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))
      (hσ.measurableSpace_mono (σn.isStoppingTime m) (σn.le m) _ hs)
  refine tendsto_nhds_unique (f := (fun m ↦ ∫ (ω : Ω) in s, stoppedValue X (τn' m) ω ∂μ))
    (l := atTop) ?_ (this ▸ ?_)
  · refine tendsto_setIntegral_of_L1' _ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
        (fun _ ↦ min_le_of_left_le <| hτ_le _) τn').aestronglyMeasurable ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le h hRC τn'
        (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le)) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
      (DiscreteApproxSequence.isStoppingTime _ _)
      (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le m)
      (DiscreteApproxSequence.countable _ m))⟩
  · refine tendsto_setIntegral_of_L1' _ hintgbl.aestronglyMeasurable ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))⟩

-- TODO: change name of `stoppedValue_min_ae_eq_condExp` in mathlib and remove the prime here
/-- **Optional sampling theorem** for approximable time indices. -/
theorem stoppedValue_min_ae_eq_condExp'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] :=
  stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC hτ hσ hτ_le
    (hτ.discreteApproxSequence μ) (hσ.discreteApproxSequence μ)

theorem stoppedValue_ae_eq_condExp_of_le_const'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC
    (isStoppingTime_const 𝓕 n) hτ (fun _ ↦ le_rfl) (discreteApproxSequence_const 𝓕 n)
      (hτ.discreteApproxSequence μ) using 2
  ext ω
  rw [eq_comm, min_eq_right_iff]
  exact hτ_le ω

theorem condExp_stoppedValue_ae_eq_stoppedProcess [Approximable 𝓕 μ] {n : ι}
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι) :
    μ[stoppedValue X τ|𝓕 i] =ᵐ[μ] stoppedProcess X τ i := by
  simp_rw [stoppedProcess_eq_stoppedValue, min_comm]
  exact EventuallyEq.trans (Eq.eventuallyEq <| by simp)
    (stoppedValue_min_ae_eq_condExp' h hRC hτ (isStoppingTime_const 𝓕 i) hτ_le).symm

end Martingale

section subsupermartingale

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Nat

variable {σ τ : Ω → WithTop ℕ} {X : ℕ → Ω → E} (𝓕 : Filtration ℕ mΩ)

-- One-step stopped-submartingale inequality for a bounded natural-time stop.
private theorem Submartingale.stoppedValue_min_const_succ_ae_le_condExp_nat
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) ≤ᵐ[P]
      P[stoppedValue X (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ))|𝓕 n] := by
  classical
  let A : Set Ω := {ω | τ ω ≤ (n : WithTop ℕ)}
  have hA : MeasurableSet[𝓕 n] A := hτ n
  have hτn : IsStoppingTime 𝓕 (τ ⊓ fun _ => (n : WithTop ℕ)) :=
    hτ.min (isStoppingTime_const 𝓕 n)
  have hτn_le : ∀ ω, (τ ⊓ fun _ => (n : WithTop ℕ)) ω ≤ n := fun ω =>
    min_le_right _ _
  have hτsn : IsStoppingTime 𝓕 (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ)) :=
    hτ.min (isStoppingTime_const 𝓕 (n + 1))
  have hτsn_le : ∀ ω, (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ)) ω ≤ n + 1 := fun ω =>
    min_le_right _ _
  have hS_n_int : Integrable (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) P :=
    hX.integrable_stoppedValue hτn hτn_le
  have hS_sn_int :
      Integrable (stoppedValue X (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ))) P :=
    hX.integrable_stoppedValue hτsn hτsn_le
  have hS_n_meas :
      StronglyMeasurable[𝓕 n] (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) :=
    stronglyMeasurable_stoppedValue_of_le
      hX.stronglyAdapted.isStronglyProgressive_of_discrete hτn hτn_le
  have hS_succ_eq :
      stoppedValue X (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ)) =ᵐ[P]
        A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) +
          Aᶜ.indicator (X (n + 1)) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ A
    · have hτ_le : τ ω ≤ (n : WithTop ℕ) := hω
      have hmin_n : min (τ ω) (n : WithTop ℕ) = τ ω := min_eq_left hτ_le
      have hmin_succ : min (τ ω) ((n + 1 : ℕ) : WithTop ℕ) = τ ω :=
        min_eq_left (hτ_le.trans (by norm_num))
      rw [stoppedValue, Pi.inf_apply, hmin_succ]
      simp [A, hω, stoppedValue, Pi.inf_apply, hmin_n]
    · have hn_lt : (n : WithTop ℕ) < τ ω := lt_of_not_ge hω
      have hn_succ_le : ((n + 1 : ℕ) : WithTop ℕ) ≤ τ ω := by
        cases hτtop : τ ω with
        | top => simp
        | coe m =>
            rw [hτtop] at hn_lt
            exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hn_lt))
      have hmin_n : min (τ ω) (n : WithTop ℕ) = (n : WithTop ℕ) := min_eq_right hn_lt.le
      have hmin_succ : min (τ ω) ((n + 1 : ℕ) : WithTop ℕ) =
          ((n + 1 : ℕ) : WithTop ℕ) := min_eq_right hn_succ_le
      rw [stoppedValue, Pi.inf_apply, hmin_succ]
      rw [Pi.add_apply, Set.indicator_of_notMem hω,
        Set.indicator_of_mem (show ω ∈ Aᶜ from hω)]
      rw [zero_add]
      change X (n + 1) ω = X (n + 1) ω
      rfl
  have hS_n_eq :
      stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) =ᵐ[P]
        A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) +
          Aᶜ.indicator (X n) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ A
    · simp [A, hω]
    · have hmin_n : min (τ ω) (n : WithTop ℕ) = (n : WithTop ℕ) :=
        min_eq_right (le_of_lt (lt_of_not_ge hω))
      rw [stoppedValue, Pi.inf_apply, hmin_n]
      rw [Pi.add_apply, Set.indicator_of_notMem hω,
        Set.indicator_of_mem (show ω ∈ Aᶜ from hω)]
      rw [zero_add]
      change X n ω = X n ω
      rfl
  have hcond_succ :
      P[stoppedValue X (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ))|𝓕 n] =ᵐ[P]
        A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) +
          Aᶜ.indicator (P[X (n + 1)|𝓕 n]) := by
    calc
      P[stoppedValue X (τ ⊓ fun _ => ((n + 1 : ℕ) : WithTop ℕ))|𝓕 n]
          =ᵐ[P] P[A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) +
            Aᶜ.indicator (X (n + 1))|𝓕 n] := condExp_congr_ae hS_succ_eq
      _ =ᵐ[P] P[A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)))|𝓕 n] +
            P[Aᶜ.indicator (X (n + 1))|𝓕 n] := by
          exact condExp_add (hS_n_int.indicator (𝓕.le n _ hA))
            ((hX.integrable (n + 1)).indicator (𝓕.le n _ hA.compl)) (𝓕 n)
      _ =ᵐ[P] A.indicator (P[stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))|𝓕 n]) +
            Aᶜ.indicator (P[X (n + 1)|𝓕 n]) := by
          exact (condExp_indicator hS_n_int hA).add
            (condExp_indicator (hX.integrable (n + 1)) hA.compl)
      _ =ᵐ[P] A.indicator (stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ))) +
            Aᶜ.indicator (P[X (n + 1)|𝓕 n]) := by
          rw [condExp_of_stronglyMeasurable (𝓕.le n) hS_n_meas hS_n_int]
  filter_upwards [hS_n_eq, hcond_succ, hX.ae_le_condExp (Nat.le_succ n)] with
    ω hleft hright hstep
  rw [hleft, hright]
  by_cases hω : ω ∈ A
  · simp [A, hω]
  · have hωc : ω ∈ Aᶜ := hω
    simpa [A, hω, hωc] using hstep

-- Deterministic-time domination by the terminal stopped value on a finite horizon.
private theorem Submartingale.stoppedValue_min_const_ae_le_condExp_nat_of_forall_le
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) {k n : ℕ} (hτk : ∀ ω, τ ω ≤ k)
    (hτ : IsStoppingTime 𝓕 τ) (hnk : n ≤ k) :
    stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) ≤ᵐ[P]
      P[stoppedValue X τ|𝓕 n] := by
  classical
  have hτ_int : Integrable (stoppedValue X τ) P :=
    hX.integrable_stoppedValue hτ hτk
  refine Nat.decreasingInduction (n := k)
    (motive := fun n _ =>
      stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) ≤ᵐ[P]
        P[stoppedValue X τ|𝓕 n]) ?step ?base hnk
  · intro m hmk ih
    have hτsm : IsStoppingTime 𝓕 (τ ⊓ fun _ => ((m + 1 : ℕ) : WithTop ℕ)) :=
      hτ.min (isStoppingTime_const 𝓕 (m + 1))
    have hτsm_le : ∀ ω, (τ ⊓ fun _ => ((m + 1 : ℕ) : WithTop ℕ)) ω ≤ m + 1 :=
      fun ω => min_le_right _ _
    have hS_succ_int :
        Integrable (stoppedValue X (τ ⊓ fun _ => ((m + 1 : ℕ) : WithTop ℕ))) P :=
      hX.integrable_stoppedValue hτsm hτsm_le
    have hone :
        stoppedValue X (τ ⊓ fun _ => (m : WithTop ℕ)) ≤ᵐ[P]
          P[stoppedValue X (τ ⊓ fun _ => ((m + 1 : ℕ) : WithTop ℕ))|𝓕 m] :=
      hX.stoppedValue_min_const_succ_ae_le_condExp_nat 𝓕 hτ m
    have hmono :
        P[stoppedValue X (τ ⊓ fun _ => ((m + 1 : ℕ) : WithTop ℕ))|𝓕 m] ≤ᵐ[P]
          P[P[stoppedValue X τ|𝓕 (m + 1)]|𝓕 m] :=
      condExp_mono hS_succ_int integrable_condExp ih
    have htower :
        P[P[stoppedValue X τ|𝓕 (m + 1)]|𝓕 m] =ᵐ[P]
          P[stoppedValue X τ|𝓕 m] :=
      condExp_condExp_of_le (𝓕.mono (Nat.le_succ m)) (𝓕.le (m + 1))
    exact hone.trans (hmono.trans htower.le)
  · have hτ_meas : StronglyMeasurable[𝓕 k] (stoppedValue X τ) :=
      stronglyMeasurable_stoppedValue_of_le
        hX.stronglyAdapted.isStronglyProgressive_of_discrete hτ hτk
    have hleft :
        stoppedValue X (τ ⊓ fun _ => (k : WithTop ℕ)) =ᵐ[P] stoppedValue X τ := by
      refine Eventually.of_forall fun ω => ?_
      have hmin : min (τ ω) (k : WithTop ℕ) = τ ω := min_eq_left (hτk ω)
      simp [stoppedValue, Pi.inf_apply, hmin]
    have hright : P[stoppedValue X τ|𝓕 k] = stoppedValue X τ :=
      condExp_of_stronglyMeasurable (𝓕.le k) hτ_meas hτ_int
    filter_upwards [hleft] with ω hω
    rw [hω, hright]

-- Finite-horizon optional sampling under the sigma-finite filtration hypotheses required by the
-- stopping-time conditional-expectation restriction lemmas.
private theorem Submartingale.stoppedValue_min_ae_le_condExp_nat_of_forall_le_of_sigmaFinite
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ ω, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  classical
  let fτ := stoppedValue X τ
  let p : Ω → Prop := fun ω =>
    stoppedValue X (τ ⊓ σ) ω ≤ P[stoppedValue X τ|hσ.measurableSpace] ω
  have hτ_int : Integrable fτ P := hX.integrable_stoppedValue hτ hτk
  have hτ_meas_k : StronglyMeasurable[𝓕 k] fτ :=
    stronglyMeasurable_stoppedValue_of_le
      hX.stronglyAdapted.isStronglyProgressive_of_discrete hτ hτk
  have hpieces :
      ∀ i ∈ Set.range σ, ∀ᵐ ω ∂P.restrict {ω | σ ω = i}, p ω := by
    intro i hi
    cases i with
    | top =>
        have htop_meas : MeasurableSet[hσ.measurableSpace] {ω : Ω | σ ω = ⊤} := by
          rw [hσ.measurableSet]
          refine ⟨hσ.measurableSet_eq_top, fun n => ?_⟩
          have hempty : {ω : Ω | σ ω = ⊤} ∩ {ω | σ ω ≤ n} = ∅ := by
            ext ω
            constructor
            · rintro ⟨hσtop, hσle⟩
              have hσtop' : σ ω = ⊤ := hσtop
              have hσle' : σ ω ≤ (n : WithTop ℕ) := hσle
              rw [hσtop'] at hσle'
              simp at hσle'
            · intro h
              cases h
          simp [hempty]
        haveI : SigmaFinite (P.trim (le_rfl : mΩ ≤ mΩ)) :=
          sigmaFiniteTrim_mono (μ := P) (m := mΩ) (m₂ := 𝓕 ⊥) (m0 := mΩ)
            le_rfl (𝓕.le ⊥)
        have h_eq_on :
            ∀ t, MeasurableSet[hσ.measurableSpace] ({ω : Ω | σ ω = ⊤} ∩ t) ↔
              MeasurableSet[mΩ] ({ω : Ω | σ ω = ⊤} ∩ t) := by
          intro t
          constructor
          · exact fun ht => hσ.measurableSpace_le _ ht
          · intro ht
            rw [hσ.measurableSet]
            refine ⟨ht, fun n => ?_⟩
            have hempty : ({ω : Ω | σ ω = ⊤} ∩ t) ∩ {ω | σ ω ≤ n} = ∅ := by
              ext ω
              constructor
              · rintro ⟨⟨hσtop, _⟩, hσle⟩
                have hσtop' : σ ω = ⊤ := hσtop
                have hσle' : σ ω ≤ (n : WithTop ℕ) := hσle
                rw [hσtop'] at hσle'
                simp at hσle'
              · intro h
                cases h
            simp [hempty]
        have hce_top :
            P[fτ|hσ.measurableSpace] =ᵐ[P.restrict {ω : Ω | σ ω = ⊤}] P[fτ|mΩ] :=
          condExp_ae_eq_restrict_of_measurableSpace_eq_on
            hσ.measurableSpace_le le_rfl htop_meas h_eq_on
        have hfτ_full : P[fτ|mΩ] = fτ :=
          condExp_of_stronglyMeasurable le_rfl (hτ_meas_k.mono (𝓕.le k)) hτ_int
        have hleft :
            stoppedValue X (τ ⊓ σ) =ᵐ[P.restrict {ω : Ω | σ ω = ⊤}] fτ := by
          filter_upwards [self_mem_ae_restrict
              (show MeasurableSet {ω : Ω | σ ω = ⊤} from hσ.measurableSet_eq_top)]
            with ω hω
          have hmin : min (τ ω) (σ ω) = τ ω := by
            rw [hω]
            exact min_eq_left le_top
          simp [fτ, stoppedValue, Pi.inf_apply, hmin]
        filter_upwards [hleft, hce_top] with ω hleftω hceω
        dsimp [p]
        rw [hleftω, hceω, hfτ_full]
    | coe n =>
        have hce_piece :
            P[fτ|hσ.measurableSpace] =ᵐ[P.restrict {ω : Ω | σ ω = (n : WithTop ℕ)}]
              P[fτ|𝓕 n] :=
          condExp_stopping_time_ae_eq_restrict_eq_of_countable hσ n
        by_cases hnk : n ≤ k
        · have hdet :
              stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) ≤ᵐ[P] P[fτ|𝓕 n] :=
            hX.stoppedValue_min_const_ae_le_condExp_nat_of_forall_le 𝓕 hτk hτ hnk
          have hleft :
              stoppedValue X (τ ⊓ σ) =ᵐ[P.restrict {ω : Ω | σ ω = (n : WithTop ℕ)}]
                stoppedValue X (τ ⊓ fun _ => (n : WithTop ℕ)) := by
            filter_upwards [self_mem_ae_restrict
                (show MeasurableSet {ω : Ω | σ ω = (n : WithTop ℕ)} from
                  𝓕.le n _ (hσ.measurableSet_eq n))]
              with ω hω
            simp [stoppedValue, Pi.inf_apply, hω]
          filter_upwards [hleft, ae_restrict_of_ae hdet, hce_piece] with ω hleftω hdetω hceω
          dsimp [p]
          rw [hleftω, hceω]
          exact hdetω
        · have hkn : k ≤ n := Nat.le_of_not_ge hnk
          have hτ_meas_n : StronglyMeasurable[𝓕 n] fτ :=
            hτ_meas_k.mono (𝓕.mono hkn)
          have hfτ_n : P[fτ|𝓕 n] = fτ :=
            condExp_of_stronglyMeasurable (𝓕.le n) hτ_meas_n hτ_int
          have hleft :
              stoppedValue X (τ ⊓ σ) =ᵐ[P.restrict {ω : Ω | σ ω = (n : WithTop ℕ)}] fτ := by
            filter_upwards [self_mem_ae_restrict
                (show MeasurableSet {ω : Ω | σ ω = (n : WithTop ℕ)} from
                  𝓕.le n _ (hσ.measurableSet_eq n))]
              with ω hω
            have hτ_le_n : τ ω ≤ (n : WithTop ℕ) :=
              (hτk ω).trans (by exact_mod_cast hkn)
            have hmin : min (τ ω) (σ ω) = τ ω := by
              rw [hω]
              exact min_eq_left hτ_le_n
            simp [fτ, stoppedValue, Pi.inf_apply, hmin]
          filter_upwards [hleft, hce_piece] with ω hleftω hceω
          dsimp [p]
          rw [hleftω, hceω, hfτ_n]
  have huniv : Set.univ = ⋃ i ∈ Set.range σ, {ω : Ω | σ ω = i} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hglobal : ∀ᵐ ω ∂P.restrict Set.univ, p ω := by
    rw [huniv]
    exact (ae_restrict_biUnion_iff (μ := P) (fun i => {ω : Ω | σ ω = i})
      (Set.to_countable (Set.range σ)) p).2 hpieces
  simpa [p] using hglobal

private theorem Submartingale.stoppedValue_min_ae_le_condExp_nat_of_forall_le [PartialOrder E]
    [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ ω, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] :=
  hX.stoppedValue_min_ae_le_condExp_nat_of_forall_le_of_sigmaFinite 𝓕 hτk hσ hτ

theorem Submartingale.stoppedValue_min_ae_le_condExp_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  let τ' : Ω → WithTop ℕ := τ ⊓ fun _ => (k : WithTop ℕ)
  have hτ' : IsStoppingTime 𝓕 τ' := hτ.min (isStoppingTime_const 𝓕 k)
  have hτ'_le : ∀ ω, τ' ω ≤ k := fun ω => min_le_right _ _
  have hτ'_ae_eq : τ' =ᵐ[P] τ := by
    filter_upwards [hτk] with ω hω
    exact min_eq_left hω
  have hleft_eq : stoppedValue X (τ' ⊓ σ) =ᵐ[P] stoppedValue X (τ ⊓ σ) := by
    filter_upwards [hτ'_ae_eq] with ω hω
    simp [stoppedValue, Pi.inf_apply, hω]
  have hright_eq : P[stoppedValue X τ'|hσ.measurableSpace] =ᵐ[P]
      P[stoppedValue X τ|hσ.measurableSpace] := by
    exact condExp_congr_ae <| by
      filter_upwards [hτ'_ae_eq] with ω hω
      simp [stoppedValue, hω]
  have hcore :
      stoppedValue X (τ' ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ'|hσ.measurableSpace] :=
    hX.stoppedValue_min_ae_le_condExp_nat_of_forall_le 𝓕 hτ'_le hσ hτ'
  filter_upwards [hcore, hleft_eq, hright_eq] with ω hle hleft hright
  simpa [← hleft, ← hright] using hle

theorem Supermartingale.condExp_ae_le_stoppedValue_min_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Supermartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    P[stoppedValue X τ|hσ.measurableSpace] ≤ᵐ[P] stoppedValue X (τ ⊓ σ) := by
  have hXneg : Submartingale (-X) 𝓕 P := hX.neg
  have h1 := hXneg.stoppedValue_min_ae_le_condExp_nat 𝓕 hτk hσ hτ
  have hsvn : ∀ τ', stoppedValue (-X) τ' = -stoppedValue X τ' := fun τ' => by
    ext ω; simp [stoppedValue]
  rw [hsvn, hsvn] at h1
  exact (h1.trans (condExp_neg (stoppedValue X τ) hσ.measurableSpace).le).mono
    fun ω hω => neg_le_neg_iff.mp hω

end Nat

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {σ τ : Ω → WithTop ι} {X : ι → Ω → E} (𝓕 : Filtration ι mΩ)

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [SecondCountableTopology ι]
  [BorelSpace ι] [MetrizableSpace ι] in
-- Transport the closed natural-time optional-sampling theorem through an indexed subfiltration.
-- Finite-range/countable-range bridges can use this once they have constructed the representing
-- natural-valued stopping times and compared the generated stopping-time sigma-algebras.
theorem Submartingale.stoppedValue_min_ae_le_condExp_of_nat_indexComap
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P) {f : ℕ → ι} (hf : Monotone f)
    {σN τN : Ω → WithTop ℕ}
    (hσ : IsStoppingTime 𝓕 σ)
    (hσN : IsStoppingTime (𝓕.indexComap hf) σN)
    (hτN : IsStoppingTime (𝓕.indexComap hf) τN) {K : ℕ}
    (hτN_le : ∀ᵐ ω ∂P, τN ω ≤ K)
    (hleft :
      stoppedValue (X ∘ f) (τN ⊓ σN) =ᵐ[P] stoppedValue X (τ ⊓ σ))
    (hterminal : stoppedValue (X ∘ f) τN =ᵐ[P] stoppedValue X τ)
    (hσ_space : hσN.measurableSpace = hσ.measurableSpace) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  have hnat :
      stoppedValue (X ∘ f) (τN ⊓ σN) ≤ᵐ[P]
        P[stoppedValue (X ∘ f) τN|hσN.measurableSpace] :=
    (hX.indexComap hf).stoppedValue_min_ae_le_condExp_nat
      (𝓕.indexComap hf) hτN_le hσN hτN
  have hright :
      P[stoppedValue (X ∘ f) τN|hσN.measurableSpace] =ᵐ[P]
        P[stoppedValue X τ|hσ.measurableSpace] := by
    rw [hσ_space]
    exact condExp_congr_ae hterminal
  filter_upwards [hnat, hleft, hright] with ω hle hleftω hrightω
  rw [← hleftω, ← hrightω]
  exact hle

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [SecondCountableTopology ι]
  [BorelSpace ι] [MetrizableSpace ι] in
/-- Countable-range submartingale optional sampling, once the countable ranges have been
represented by a monotone natural-time skeleton.  The explicit representation hypotheses are the
honest missing data for infinite countable ranges; finite-range enumerations should discharge
them by constructing `f`, `τN`, and `σN` from the finite ordered range. -/
theorem Submartingale.stoppedValue_min_ae_le_condExp_of_countable_range
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ)
    (hσ_countable_range : (Set.range σ).Countable)
    (hτ_countable_range : (Set.range τ).Countable)
    {f : ℕ → ι} (hf : Monotone f) {σN τN : Ω → WithTop ℕ}
    (hσN : IsStoppingTime (𝓕.indexComap hf) σN)
    (hτN : IsStoppingTime (𝓕.indexComap hf) τN) {K : ℕ}
    (hτN_le : ∀ᵐ ω ∂P, τN ω ≤ K)
    (hleft_idx : ∀ ω, f ((τN ⊓ σN) ω).untopA = ((τ ⊓ σ) ω).untopA)
    (hterminal_idx : ∀ ω, f (τN ω).untopA = (τ ω).untopA)
    (hσ_space : hσN.measurableSpace = hσ.measurableSpace) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  -- The countability hypotheses document the intended source of the representation package.
  -- They are not enough by themselves in this ordered-Banach generality.
  have _ : IsStoppingTime 𝓕 τ := hτ
  have _ : (Set.range σ).Countable := hσ_countable_range
  have _ : (Set.range τ).Countable := hτ_countable_range
  have hleft :
      stoppedValue (X ∘ f) (τN ⊓ σN) =ᵐ[P] stoppedValue X (τ ⊓ σ) := by
    refine Eventually.of_forall fun ω => ?_
    change X (f (((τN ⊓ σN) ω).untopA)) ω = X (((τ ⊓ σ) ω).untopA) ω
    rw [hleft_idx ω]
  have hterminal :
      stoppedValue (X ∘ f) τN =ᵐ[P] stoppedValue X τ := by
    refine Eventually.of_forall fun ω => ?_
    simp [stoppedValue, hterminal_idx ω]
  exact hX.stoppedValue_min_ae_le_condExp_of_nat_indexComap 𝓕 hf hσ
    hσN hτN hτN_le hleft hterminal hσ_space

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [SecondCountableTopology ι]
  [BorelSpace ι] [MetrizableSpace ι] in
/-- Finite-range submartingale optional sampling from a represented finite natural skeleton.
The hypotheses `hσ_cut` and `hτ_cut` say that the natural ranks have exactly the same stopping
cuts as the original stopping times along the monotone skeleton `f`; the finite bound on `σN`
is used only to identify the stopping-time sigma-algebra of `σN` with that of `σ`. -/
theorem Submartingale.stoppedValue_min_ae_le_condExp_of_finite_range
    [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕]
    (hX : Submartingale X 𝓕 P)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ)
    {K : ℕ} {k : ι} {f : ℕ → ι} (hf : Monotone f) (hk : f K = k)
    (hτk : ∀ ω, τ ω ≤ k) {σN τN : Ω → WithTop ℕ}
    (hσN_top_or_le : ∀ ω, σN ω = ⊤ ∨ σN ω ≤ (K : WithTop ℕ))
    (hτN_le : ∀ ω, τN ω ≤ (K : WithTop ℕ))
    (hσ_repr : ∀ ω, WithTop.map f (σN ω) = σ ω)
    (hτ_repr : ∀ ω, WithTop.map f (τN ω) = τ ω)
    (hσ_cut : ∀ n : ℕ, {ω : Ω | σN ω ≤ (n : WithTop ℕ)} =
      {ω | σ ω ≤ (f n : WithTop ι)})
    (hτ_cut : ∀ n : ℕ, {ω : Ω | τN ω ≤ (n : WithTop ℕ)} =
      {ω | τ ω ≤ (f n : WithTop ι)}) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  classical
  have _ : ∀ ω, τ ω ≤ k := hτk
  have _ : f K = k := hk
  have hσN : IsStoppingTime (𝓕.indexComap hf) σN := by
    intro n
    change MeasurableSet[𝓕 (f n)] {ω : Ω | σN ω ≤ (n : WithTop ℕ)}
    rw [hσ_cut n]
    exact hσ (f n)
  have hτN : IsStoppingTime (𝓕.indexComap hf) τN := by
    intro n
    change MeasurableSet[𝓕 (f n)] {ω : Ω | τN ω ≤ (n : WithTop ℕ)}
    rw [hτ_cut n]
    exact hτ (f n)
  have hσ_countable_range : (Set.range σ).Countable := by
    refine (Set.countable_range (fun n : WithTop ℕ => WithTop.map f n)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨σN ω, hσ_repr ω⟩
  have hτ_countable_range : (Set.range τ).Countable := by
    refine (Set.countable_range (fun n : WithTop ℕ => WithTop.map f n)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨τN ω, hτ_repr ω⟩
  have hτN_le_ae : ∀ᵐ ω ∂P, τN ω ≤ (K : WithTop ℕ) :=
    ae_of_all _ hτN_le
  have hterminal_idx : ∀ ω, f (τN ω).untopA = (τ ω).untopA := by
    intro ω
    have hτN_ne_top : τN ω ≠ ⊤ := by
      intro htop
      have : (⊤ : WithTop ℕ) ≤ (K : WithTop ℕ) := by
        simpa [htop] using hτN_le ω
      simp at this
    cases hτNω : τN ω with
    | top => exact False.elim (hτN_ne_top hτNω)
    | coe n =>
        simpa [hτNω] using (congrArg WithTop.untopA (hτ_repr ω).symm).symm
  have hleft_idx : ∀ ω, f ((τN ⊓ σN) ω).untopA = ((τ ⊓ σ) ω).untopA := by
    intro ω
    have hτN_ne_top : τN ω ≠ ⊤ := by
      intro htop
      have : (⊤ : WithTop ℕ) ≤ (K : WithTop ℕ) := by
        simpa [htop] using hτN_le ω
      simp at this
    cases hτNω : τN ω with
    | top => exact False.elim (hτN_ne_top hτNω)
    | coe n =>
        cases hσNω : σN ω with
        | top =>
            have hτ_eq : τ ω = (f n : WithTop ι) := by
              simpa [hτNω] using (hτ_repr ω).symm
            have hσ_eq : σ ω = ⊤ := by
              simpa [hσNω] using (hσ_repr ω).symm
            rw [Pi.inf_apply, hτNω, hσNω]
            change f n = (min (τ ω) (σ ω)).untopA
            rw [hτ_eq, hσ_eq]
            change f n = f n
            rfl
        | coe m =>
            have hτ_eq : τ ω = (f n : WithTop ι) := by
              simpa [hτNω] using (hτ_repr ω).symm
            have hσ_eq : σ ω = (f m : WithTop ι) := by
              simpa [hσNω] using (hσ_repr ω).symm
            rw [Pi.inf_apply, hτNω, hσNω]
            change f (min n m) = (min (τ ω) (σ ω)).untopA
            rw [hτ_eq, hσ_eq]
            change f (min n m) = min (f n) (f m)
            exact hf.map_min
  have hσ_space : hσN.measurableSpace = hσ.measurableSpace := by
    ext s
    constructor
    · intro hs
      rw [IsStoppingTime.measurableSet]
      refine ⟨hs.1, fun i => ?_⟩
      have hdecomp :
          s ∩ {ω : Ω | σ ω ≤ (i : WithTop ι)} =
            ⋃ n : Fin (K + 1),
              if f n ≤ i then s ∩ {ω : Ω | σN ω = (n : ℕ)} else ∅ := by
        ext ω
        constructor
        · rintro ⟨hωs, hσi⟩
          rcases hσN_top_or_le ω with htop | hleK
          · have hσ_top : σ ω = ⊤ := by
              simpa [htop] using (hσ_repr ω).symm
            simp [hσ_top] at hσi
          · cases hσNω : σN ω with
            | top =>
                have : (⊤ : WithTop ℕ) ≤ (K : WithTop ℕ) := by
                  rw [← hσNω]
                  exact hleK
                simp at this
            | coe m =>
                have hmK : m ≤ K := by
                  simpa [hσNω] using hleK
                refine Set.mem_iUnion.2 ⟨⟨m, Nat.lt_succ_of_le hmK⟩, ?_⟩
                have hσ_eq : σ ω = (f m : WithTop ι) := by
                  simpa [hσNω] using (hσ_repr ω).symm
                have hfmi : f m ≤ i := by
                  simpa [hσ_eq] using hσi
                simp [hfmi, hωs, hσNω]
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
          by_cases hfi : f n ≤ i
          · rw [if_pos hfi] at hn
            exact ⟨hn.1, by
              have hσ_eq : σ ω = (f n : WithTop ι) := by
                rw [← hσ_repr ω, hn.2]
                simp
              simpa [hσ_eq] using hfi⟩
          · rw [if_neg hfi] at hn
            exact False.elim hn
      rw [hdecomp]
      refine MeasurableSet.iUnion fun n => ?_
      by_cases hfi : f n ≤ i
      · rw [if_pos hfi]
        have hlevel_ms :
            MeasurableSet[hσN.measurableSpace] {ω : Ω | σN ω = (n : ℕ)} := by
          rw [← Set.univ_inter {ω : Ω | σN ω = (n : ℕ)}]
          exact (hσN.measurableSet_inter_eq_iff Set.univ n).2 (by
            simpa using hσN.measurableSet_eq n)
        have hlevel :
            MeasurableSet[𝓕 (f n)] (s ∩ {ω : Ω | σN ω = (n : ℕ)}) :=
          (hσN.measurableSet_inter_eq_iff s n).1 (hs.inter hlevel_ms)
        exact 𝓕.mono hfi _ hlevel
      · rw [if_neg hfi]
        exact @MeasurableSet.empty _ (𝓕 i)
    · intro hs
      rw [IsStoppingTime.measurableSet]
      refine ⟨hs.1, fun n => ?_⟩
      change MeasurableSet[𝓕 (f n)] (s ∩ {ω : Ω | σN ω ≤ (n : WithTop ℕ)})
      rw [hσ_cut n]
      exact hs.2 (f n)
  exact hX.stoppedValue_min_ae_le_condExp_of_countable_range 𝓕 hσ hτ
    hσ_countable_range hτ_countable_range hf hσN hτN hτN_le_ae
    hleft_idx hterminal_idx hσ_space

omit [CompleteSpace E] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι]
  [MetrizableSpace ι] in
/-- Integrability of a bounded stopped value from explicit uniform integrability of its
discrete approximants.  This is the honest submartingale substrate: the uniform integrability
assumption is not derived from the one-sided optional-sampling inequality. -/
lemma Submartingale.integrable_stoppedValue_of_discreteApproxSequence_of_uniformIntegrable
    [LE E] [IsFiniteMeasure P]
    (hX : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτ_le : ∀ ω, τ ω ≤ k) (τn : DiscreteApproxSequence 𝓕 τ P)
    (hUI : UniformIntegrable
      (fun n ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn n)) 1 P) :
    Integrable (stoppedValue X τ) P := by
  have _ : StronglyAdapted 𝓕 X := hX.stronglyAdapted
  rw [← memLp_one_iff_integrable]
  exact hUI.memLp_of_tendstoInMeasure <|
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hUI.memLp n).integrable le_rfl).1)
      (tendsto_stoppedValue_discreteApproxSequence
        (discreteApproxSequence_of 𝓕 hτ_le τn) hX2)

omit [CompleteSpace E] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι]
  [MetrizableSpace ι] in
/-- `L¹` convergence of stopped values along bounded discrete approximations, assuming explicit
uniform integrability. -/
lemma Submartingale.tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_uniformIntegrable
    [LE E] [IsFiniteMeasure P]
    (hX : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτ_le : ∀ ω, τ ω ≤ k) (τn : DiscreteApproxSequence 𝓕 τ P)
    (hUI : UniformIntegrable
      (fun n ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn n)) 1 P) :
    Tendsto (fun n ↦
      eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn n) -
        stoppedValue X τ) 1 P) atTop (𝓝 0) := by
  refine tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ ((hUI.memLp n).integrable le_rfl).1)
    (memLp_one_iff_integrable.2
      (hX.integrable_stoppedValue_of_discreteApproxSequence_of_uniformIntegrable
        𝓕 hX2 hτ_le τn hUI))
    hUI.2.1 ?_
  exact tendstoInMeasure_of_tendsto_ae
    (fun n ↦ ((hUI.memLp n).integrable le_rfl).1)
    (tendsto_stoppedValue_discreteApproxSequence
      (discreteApproxSequence_of 𝓕 hτ_le τn) hX2)

theorem Submartingale.stoppedValue_min_ae_le_condExp [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτk : ∀ᵐ ω ∂P, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  let τ' : Ω → WithTop ι := τ ⊓ fun _ => (k : WithTop ι)
  have hτ' : IsStoppingTime 𝓕 τ' := hτ.min (isStoppingTime_const 𝓕 k)
  have hτ'_le : ∀ ω, τ' ω ≤ k := fun ω => min_le_right _ _
  have hτ'_ae_eq : τ' =ᵐ[P] τ := by
    filter_upwards [hτk] with ω hω
    exact min_eq_left hω
  have hleft_eq : stoppedValue X (τ' ⊓ σ) =ᵐ[P] stoppedValue X (τ ⊓ σ) := by
    filter_upwards [hτ'_ae_eq] with ω hω
    simp [stoppedValue, Pi.inf_apply, hω]
  have hright_eq : P[stoppedValue X τ'|hσ.measurableSpace] =ᵐ[P]
      P[stoppedValue X τ|hσ.measurableSpace] := by
    exact condExp_congr_ae <| by
      filter_upwards [hτ'_ae_eq] with ω hω
      simp [stoppedValue, hω]
  have hL1_terminal :
      ∀ [IsFiniteMeasure P] (τn : DiscreteApproxSequence 𝓕 τ' P),
        UniformIntegrable
          (fun n ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ'_le τn n)) 1 P →
        Tendsto (fun n ↦
          eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ'_le τn n) -
            stoppedValue X τ') 1 P) atTop (𝓝 0) := by
    intro _ τn hUI
    exact hX1.tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_uniformIntegrable
      𝓕 hX2 hτ'_le τn hUI
  have hτ'σ_le : ∀ ω, (τ' ⊓ σ) ω ≤ k := fun ω =>
    min_le_of_left_le (hτ'_le ω)
  have hL1_min :
      ∀ [IsFiniteMeasure P] (ρn : DiscreteApproxSequence 𝓕 (τ' ⊓ σ) P),
        UniformIntegrable
          (fun n ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ'σ_le ρn n)) 1 P →
        Tendsto (fun n ↦
          eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ'σ_le ρn n) -
            stoppedValue X (τ' ⊓ σ)) 1 P) atTop (𝓝 0) := by
    intro _ ρn hUI
    exact hX1.tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_uniformIntegrable
      𝓕 hX2 hτ'σ_le ρn hUI
  -- The closed `hL1_terminal` and `hL1_min` substrates give the two L¹ convergence steps once
  -- the theorem surface supplies `[Approximable 𝓕 P]`, `[IsFiniteMeasure P]`, and the required
  -- uniform integrability hypotheses.  The remaining gap is the countable-range submartingale
  -- optional-sampling inequality for the approximants, followed by the set-integral limit
  -- passage and transport through `hleft_eq`/`hright_eq`.
  sorry

end subsupermartingale

end MeasureTheory
