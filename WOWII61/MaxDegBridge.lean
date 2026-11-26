module

public import WOWII61.GraphToHH
public import WOWII61.SimultaneousPairBound

/-!
# Bridge to `WOWII61.PackingBound.MaxDegDeletionResiduePremise` (`MaxDegBridge`)

This module bridges the graph-level positive maximum-degree vertex deletion theorem
`WOWII61.PackingBound.MaxDegDeletionResiduePremise` (from `../lean_bound/SimultaneousPairBound.lean`)
to all four purely arithmetic sequence monotonicity interfaces documented in `API.md`
(`ExchangeStep`, `DominatedBy`, multiset `d`-decrement, and indexed `d`-decrement).

It also lifts each bridge directly to the downstream theorems of `SimultaneousPairBound`:
- Theorem 1 (`simultaneous_additional_edges_of_maxDegDeletion`, `residue_le_indepNum_of_maxDegDeletion`)
- Theorem 2 (`uniform_diam_bound_of_maxDegDeletion`, `wowii61_of_twelve_diams_of_maxDegDeletion`).
-/

@[expose] public section

namespace WOWII61.ResidueGraph

open SimpleGraph Finset WOWII61.PackingBound

/-- Option A (HH-valid single exchange step monotonicity). -/
def ExchangeStepMonotonePremise : Prop :=
  ∀ s₁ s₂ : List ℕ,
    ExchangeStep s₁ s₂ → IsHHValid s₁ → IsHHValid s₂ →
    SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂

/-- Option A' (graphic single exchange step monotonicity). -/
def ExchangeStepGraphicMonotonePremise : Prop :=
  ∀ s₁ s₂ : List ℕ,
    ExchangeStep s₁ s₂ → IsGraphic s₁ → IsGraphic s₂ →
    SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂

/-- Option B (Triesch 1996 dominance monotonicity on HH-valid descending lists). -/
def DominatedByMonotonePremise : Prop :=
  ∀ s₁ s₂ : List ℕ,
    DominatedBy s₁ s₂ → IsHHValid s₁ → IsHHValid s₂ →
    SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂

/-- Option C (direct multiset `d`-decrement monotonicity vs. `havelHakimiStep`). -/
def MultisetDecrementMonotonePremise : Prop :=
  ∀ (d : ℕ) (r : List ℕ) (M_A M_B : Multiset ℕ),
    0 < d →
    (d :: r).Pairwise (· ≥ ·) →
    IsHHValid (d :: r) →
    (r : Multiset ℕ) = M_A + M_B →
    Multiset.card M_A = d →
    (∀ x ∈ M_A, 1 ≤ x) →
    IsHHValid ((M_A.map (· - 1) + M_B).sort (· ≥ ·)) →
    SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (d :: r)) ≤
      SimpleGraph.residueAux ((M_A.map (· - 1) + M_B).sort (· ≥ ·))

/-- Option D (direct indexed `d`-decrement monotonicity vs. `havelHakimiStep`). -/
def IndexedDecrementMonotonePremise : Prop :=
  ∀ (d : ℕ) (r : List ℕ) (S : Finset (Fin r.length)),
    0 < d →
    (d :: r).Pairwise (· ≥ ·) →
    IsHHValid (d :: r) →
    S.card = d →
    (∀ i ∈ S, 1 ≤ r[i]) →
    let s' := ((List.finRange r.length).map (fun i => if i ∈ S then r[i] - 1 else r[i])).mergeSort
      (· ≥ ·)
    IsHHValid s' →
    SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (d :: r)) ≤
      SimpleGraph.residueAux s'

/-- Option A and Option A' are logically equivalent via `isGraphic_iff_sorted_hhValid`. -/
theorem exchangeStepMonotone_iff_graphic :
    ExchangeStepMonotonePremise ↔ ExchangeStepGraphicMonotonePremise := by
  constructor
  · intro h s₁ s₂ hstep hg₁ hg₂
    exact h s₁ s₂ hstep (isHHValid_of_isGraphic hg₁) (isHHValid_of_isGraphic hg₂)
  · intro h s₁ s₂ hstep hv₁ hv₂
    exact h s₁ s₂ hstep
      (isGraphic_of_isHHValid hstep.1 hv₁)
      (isGraphic_of_isHHValid hstep.2.1 hv₂)

/-- Bridge from Option A (`ExchangeStepMonotonePremise`) to `MaxDegDeletionResiduePremise`. -/
theorem maxDegDeletionResiduePremise_of_exchangeStep
    (hExch : ExchangeStepMonotonePremise) : MaxDegDeletionResiduePremise := by
  intro n Q _ v hmax hpos
  rw [residue_eq_residueAux_hhStep_of_max Q v hmax hpos, residue_eq_residueAux_degList]
  have hmono : ∀ {a b : List ℕ},
      Relation.ReflTransGen (fun x y => ExchangeStep x y ∧ IsHHValid x ∧ IsHHValid y) a b →
      SimpleGraph.residueAux a ≤ SimpleGraph.residueAux b := by
    intro a b hchain
    induction hchain with
    | refl => exact le_rfl
    | tail _ hstep ih => exact ih.trans (hExch _ _ hstep.1 hstep.2.1 hstep.2.2)
  exact hmono (hhValid_exchangeStep_chain_of_maxDegDeletion Q v)

/-- Bridge from Option A' (`ExchangeStepGraphicMonotonePremise`) to `MaxDegDeletionResiduePremise`. -/
theorem maxDegDeletionResiduePremise_of_exchangeStepGraphic
    (hExch : ExchangeStepGraphicMonotonePremise) : MaxDegDeletionResiduePremise :=
  maxDegDeletionResiduePremise_of_exchangeStep (exchangeStepMonotone_iff_graphic.mpr hExch)

/-- Bridge from Option B (`DominatedByMonotonePremise`) to `MaxDegDeletionResiduePremise`. -/
theorem maxDegDeletionResiduePremise_of_dominatedBy
    (hDom : DominatedByMonotonePremise) : MaxDegDeletionResiduePremise := by
  intro n Q _ v hmax hpos
  rw [residue_eq_residueAux_hhStep_of_max Q v hmax hpos, residue_eq_residueAux_degList]
  have hdom := dominatedBy_of_maxDegDeletion Q v
  have hQ_valid : IsHHValid (Q.degree v :: restList Q v) := by
    rw [← degList_eq_cons_of_max Q v hmax]
    exact isHHValid_of_isGraphic (isGraphic_of_degList Q)
  have hHH_valid : IsHHValid (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v)) :=
    ((isHHValid_cons _ _).mp hQ_valid).2.2
  have hDel_valid : IsHHValid (degList (Q.induce { u : Fin n | u ≠ v })) :=
    isHHValid_of_isGraphic (isGraphic_of_degList _)
  exact hDom _ _ hdom hHH_valid hDel_valid

/-- Bridge from Option C (`MultisetDecrementMonotonePremise`) to `MaxDegDeletionResiduePremise`. -/
theorem maxDegDeletionResiduePremise_of_multisetDecrement
    (hMul : MultisetDecrementMonotonePremise) : MaxDegDeletionResiduePremise := by
  intro n Q _ v hmax hpos
  rw [residue_eq_residueAux_hhStep_of_max Q v hmax hpos, residue_eq_residueAux_degList]
  obtain ⟨M_A, M_B, hrest, hdel, hcard, hposA⟩ := induce_ne_degMultiset_partition Q v
  have hcons : degList Q = Q.degree v :: restList Q v := degList_eq_cons_of_max Q v hmax
  have hsort : (Q.degree v :: restList Q v).Pairwise (· ≥ ·) := hcons ▸ degList_pairwise Q
  have hQ_valid : IsHHValid (Q.degree v :: restList Q v) :=
    hcons ▸ isHHValid_of_isGraphic (isGraphic_of_degList Q)
  have hcoe : ((restList Q v : List ℕ) : Multiset ℕ) = M_A + M_B := by
    rw [restList_coe, hrest]
  have hdel_list : degList (Q.induce { u : Fin n | u ≠ v }) =
      (M_A.map (· - 1) + M_B).sort (· ≥ ·) := by
    unfold degList
    rw [hdel]
  have hdel_valid : IsHHValid ((M_A.map (· - 1) + M_B).sort (· ≥ ·)) := by
    rw [← hdel_list]
    exact isHHValid_of_isGraphic (isGraphic_of_degList _)
  rw [hdel_list]
  exact hMul (Q.degree v) (restList Q v) M_A M_B hpos hsort hQ_valid hcoe hcard hposA hdel_valid

/-- Bridge from Option D (`IndexedDecrementMonotonePremise`) to `MaxDegDeletionResiduePremise`. -/
theorem maxDegDeletionResiduePremise_of_indexedDecrement
    (hIdx : IndexedDecrementMonotonePremise) : MaxDegDeletionResiduePremise := by
  intro n Q _ v hmax hpos
  rw [residue_eq_residueAux_hhStep_of_max Q v hmax hpos, residue_eq_residueAux_degList]
  obtain ⟨S, hcard, hposS, hdel⟩ := induce_ne_degList_as_indexed_decrement Q v
  have hcons : degList Q = Q.degree v :: restList Q v := degList_eq_cons_of_max Q v hmax
  have hsort : (Q.degree v :: restList Q v).Pairwise (· ≥ ·) := hcons ▸ degList_pairwise Q
  have hQ_valid : IsHHValid (Q.degree v :: restList Q v) :=
    hcons ▸ isHHValid_of_isGraphic (isGraphic_of_degList Q)
  have hdel_merge : degList (Q.induce { u : Fin n | u ≠ v }) =
      ((List.finRange (restList Q v).length).map
        (fun i => if i ∈ S then (restList Q v)[i] - 1 else (restList Q v)[i])).mergeSort
        (· ≥ ·) := by
    rw [hdel, decrementedSort_eq_mergeSort_finRange]
  have hdel_valid : IsHHValid
      (((List.finRange (restList Q v).length).map
        (fun i => if i ∈ S then (restList Q v)[i] - 1 else (restList Q v)[i])).mergeSort
        (· ≥ ·)) := by
    rw [← hdel_merge]
    exact isHHValid_of_isGraphic (isGraphic_of_degList _)
  rw [hdel_merge]
  exact hIdx (Q.degree v) (restList Q v) S hpos hsort hQ_valid hcard hposS hdel_valid

end WOWII61.ResidueGraph
