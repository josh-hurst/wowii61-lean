module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Relation
public import WOWII61.Defs

/-!
# Graph-to-Havel–Hakimi Bridge (`GraphToHH`)

This module formalizes the exact graph-facing bridge for positive maximum-degree vertex deletion
using the exact upstream `SimpleGraph.havelHakimiStep`, `SimpleGraph.residueAux`, and
`SimpleGraph.residue` from `../lean_partial/StagedDeps/Residue.lean`:

1. **Purely arithmetic sequence predicates** (`IsHHValid`, `ExchangeStep`, `DominatedBy`):
   no dependency on `SimpleGraph`, designed for clean coordination with `../lean_residue_seq`.
2. **Degree multisets, descending degree lists, and induced vertex deletion (`Q - v`)**:
   - `degMultiset`, `degList`, `restMultiset`, `restList`, `IsGraphic`
   - `degList_eq_cons_of_max`, `residue_eq_residueAux_hhStep_of_max`
   - `induce_ne_degMultiset_partition` (exact multiset partition of `Q - v` degrees)
   - `induce_ne_degList_as_indexed_decrement` (exact `d`-element index subset of `restList Q v`)
3. **Sorted-list exchange & dominance vs. subtracting the `d` largest entries**:
   - `multiset_sum_le_take_sum` (top-`k` sum maximality for descending lists)
   - `exchangeStep_imp_dominatedBy` and `dominatedBy_of_exchangeStep_chain`
   - `exchangeStep_chain_of_subset_decrement` (swapping top `d` indices into any `d`-subset `S`
     with positive entries produces a finite chain of `ExchangeStep`s from `havelHakimiStep`
     up to the `S`-decremented sorted list)
   - `exchangeStep_chain_of_maxDegDeletion` and `dominatedBy_of_maxDegDeletion`
4. **Local degree shift (`edgeShift`) and the Classical Havel–Hakimi Theorem (both directions)**:
   - `isGraphic_of_exchangeStep`: downward graphic closure under `ExchangeStep` via single-edge
     shift (`havelHakimiStep` degree-sequence monotonicity)
   - `isGraphic_havelHakimiStep`: graphic descent of `SimpleGraph.havelHakimiStep`
   - `isHHValid_of_isGraphic`, `isGraphic_of_isHHValid`, `isGraphic_iff_sorted_hhValid`
   - `isHHValid_of_exchangeStep`, `graphic_exchangeStep_chain_of_maxDegDeletion`,
     `hhValid_exchangeStep_chain_of_maxDegDeletion`.
-/

@[expose] public section

namespace WOWII61.ResidueGraph

open SimpleGraph Finset

/-! ## 1. Purely Arithmetic Sequence Predicates -/

section SequencePredicates

/-- Purely arithmetic Havel–Hakimi validity (no underflow at any Havel–Hakimi step).
On descending sorted lists (`s.Pairwise (· ≥ ·)`), this module proves that `IsHHValid s`
is equivalent to `IsGraphic s`. -/
def IsHHValid : List ℕ → Prop
  | [] => True
  | d :: rest =>
    d ≤ rest.length ∧
    (∀ x ∈ rest.take d, 1 ≤ x) ∧
    IsHHValid (SimpleGraph.havelHakimiStep (d :: rest))
termination_by s => s.length
decreasing_by
  simp [SimpleGraph.havelHakimiStep_length_cons]

@[simp]
theorem isHHValid_nil : IsHHValid [] ↔ True := by
  rw [IsHHValid]

theorem isHHValid_cons (d : ℕ) (rest : List ℕ) :
    IsHHValid (d :: rest) ↔
      d ≤ rest.length ∧
      (∀ x ∈ rest.take d, 1 ≤ x) ∧
      IsHHValid (SimpleGraph.havelHakimiStep (d :: rest)) := by
  rw [IsHHValid]

/-- One elementary dominance / exchange transfer `(a, b) ↦ (a + 1, b - 1)` with `a ≥ b ≥ 1`
between descending sorted lists. -/
def ExchangeStep (s₁ s₂ : List ℕ) : Prop :=
  s₁.Pairwise (· ≥ ·) ∧ s₂.Pairwise (· ≥ ·) ∧
  ∃ (m : Multiset ℕ) (a b : ℕ),
    b ≤ a ∧ 1 ≤ b ∧
    (s₁ : Multiset ℕ) = a ::ₘ b ::ₘ m ∧
    (s₂ : Multiset ℕ) = (a + 1) ::ₘ (b - 1) ::ₘ m

/-- Majorization / dominance order on descending sorted lists (`s₁ ⪯ s₂`, i.e., `s₂` dominates `s₁`). -/
def DominatedBy (s₁ s₂ : List ℕ) : Prop :=
  s₁.Pairwise (· ≥ ·) ∧ s₂.Pairwise (· ≥ ·) ∧
  s₁.length = s₂.length ∧ s₁.sum = s₂.sum ∧
  ∀ k : ℕ, (s₁.take k).sum ≤ (s₂.take k).sum

theorem dominatedBy_refl {s : List ℕ} (hs : s.Pairwise (· ≥ ·)) : DominatedBy s s :=
  ⟨hs, hs, rfl, rfl, fun _ => le_rfl⟩

theorem dominatedBy_trans {s₁ s₂ s₃ : List ℕ}
    (h12 : DominatedBy s₁ s₂) (h23 : DominatedBy s₂ s₃) : DominatedBy s₁ s₃ :=
  ⟨h12.1, h23.2.1, h12.2.2.1.trans h23.2.2.1, h12.2.2.2.1.trans h23.2.2.2.1,
    fun k => (h12.2.2.2.2 k).trans (h23.2.2.2.2 k)⟩

end SequencePredicates

/-! ## 2. Basic List, Multiset, Sorting, and `havelHakimiStep` Helpers -/

section ListMultisetHelpers

/-- Two descending sorted lists with equal underlying multisets are equal. -/
theorem eq_of_pairwise_ge_of_coe_eq {l₁ l₂ : List ℕ}
    (h₁ : l₁.Pairwise (· ≥ ·)) (h₂ : l₂.Pairwise (· ≥ ·))
    (heq : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) : l₁ = l₂ :=
  (Multiset.coe_eq_coe.mp heq).eq_of_pairwise' h₁ h₂

/-- A descending sorted list equals the descending sort of its multiset. -/
theorem sort_coe_eq_self {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) :
    (l : Multiset ℕ).sort (· ≥ ·) = l :=
  eq_of_pairwise_ge_of_coe_eq (Multiset.pairwise_sort _ _) hl (Multiset.sort_eq _ _)

/-- `l.mergeSort (· ≥ ·)` is sorted descending. -/
theorem mergeSort_ge_pairwise (l : List ℕ) : (l.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
  List.pairwise_mergeSort' (r := fun a b : ℕ => a ≥ b) l

/-- `l.mergeSort (· ≥ ·)` has the same underlying multiset as `l`. -/
theorem mergeSort_ge_coe (l : List ℕ) :
    ((l.mergeSort (· ≥ ·) : List ℕ) : Multiset ℕ) = (l : Multiset ℕ) :=
  Multiset.coe_eq_coe.mpr (List.mergeSort_perm l _)

/-- `l.mergeSort (· ≥ ·)` agrees with `Multiset.sort (l : Multiset ℕ) (· ≥ ·)`. -/
theorem mergeSort_ge_eq_sort (l : List ℕ) :
    l.mergeSort (· ≥ ·) = (l : Multiset ℕ).sort (· ≥ ·) :=
  eq_of_pairwise_ge_of_coe_eq (mergeSort_ge_pairwise l) (Multiset.pairwise_sort _ _)
    (by rw [mergeSort_ge_coe, Multiset.sort_eq])

/-- `SimpleGraph.havelHakimiStep` always returns a descending sorted list. -/
theorem havelHakimiStep_pairwise (s : List ℕ) :
    (SimpleGraph.havelHakimiStep s).Pairwise (· ≥ ·) := by
  cases s with
  | nil => simp [SimpleGraph.havelHakimiStep]
  | cons d rest =>
    simp only [SimpleGraph.havelHakimiStep]
    exact mergeSort_ge_pairwise _

/-- Exact multiset formula for `SimpleGraph.havelHakimiStep (d :: rest)`. -/
theorem havelHakimiStep_coe (d : ℕ) (rest : List ℕ) :
    ((SimpleGraph.havelHakimiStep (d :: rest) : List ℕ) : Multiset ℕ) =
      (((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ) + (rest.drop d : Multiset ℕ) := by
  simp only [SimpleGraph.havelHakimiStep, List.splitAt_eq]
  rw [mergeSort_ge_coe, Multiset.coe_add]

/-- Exact sorted-multiset form of `SimpleGraph.havelHakimiStep (d :: rest)`. -/
theorem havelHakimiStep_eq_sort (d : ℕ) (rest : List ℕ) :
    SimpleGraph.havelHakimiStep (d :: rest) =
      ((((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ) + (rest.drop d : Multiset ℕ)).sort
        (· ≥ ·) :=
  eq_of_pairwise_ge_of_coe_eq (havelHakimiStep_pairwise _) (Multiset.pairwise_sort _ _)
    (by rw [havelHakimiStep_coe, Multiset.sort_eq])

/-- Unfolding `SimpleGraph.residueAux` when the head degree is positive. -/
theorem residueAux_cons_of_pos {d : ℕ} (hd : 0 < d) (rest : List ℕ) :
    SimpleGraph.residueAux (d :: rest) =
      SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (d :: rest)) := by
  cases d with
  | zero => omega
  | succ k => simp [SimpleGraph.residueAux]

/-- Descending order implies index-level antitonicity. -/
theorem pairwise_ge_getElem_le {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[j] ≤ l[i] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp hl i j hi hj hlt

/-- Submultiset decomposition against `x ::ₘ u`: either `t ≤ u` or `x` can be peeled off `t`. -/
private lemma multiset_le_cons_iff_cases {α : Type*} [DecidableEq α] {t u : Multiset α} {x : α}
    (h : t ≤ x ::ₘ u) : t ≤ u ∨ ∃ t', t = x ::ₘ t' ∧ t' ≤ u := by
  by_cases hx : x ∈ t
  · right
    refine ⟨t.erase x, (Multiset.cons_erase hx).symm, ?_⟩
    rw [← Multiset.cons_le_cons_iff x, Multiset.cons_erase hx]
    exact h
  · left
    rw [Multiset.le_iff_count] at h ⊢
    intro z
    specialize h z
    by_cases hzx : z = x
    · subst hzx
      have hc : Multiset.count z t = 0 := Multiset.count_eq_zero.mpr hx
      omega
    · rwa [Multiset.count_cons_of_ne hzx] at h

/-- **Top-`k` Sum Maximality:** in a descending list `l`, every submultiset `t ≤ l` of
cardinality at most `k` has sum at most `(l.take k).sum`. -/
theorem multiset_sum_le_take_sum {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {t : Multiset ℕ} (ht : t ≤ (l : Multiset ℕ)) (k : ℕ) (hk : t.card ≤ k) :
    t.sum ≤ (l.take k).sum := by
  induction l generalizing t k with
  | nil =>
    have ht0 : t = 0 := Multiset.le_zero.mp ht
    simp [ht0]
  | cons x xs ih =>
    rw [List.pairwise_cons] at hl
    cases k with
    | zero =>
      have ht0 : t = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp [ht0]
    | succ k' =>
      simp only [List.take_succ_cons, List.sum_cons]
      have ht' : t ≤ x ::ₘ (xs : Multiset ℕ) := by simpa using ht
      rcases multiset_le_cons_iff_cases ht' with hle_xs | ⟨t', rfl, hle_xs⟩
      · by_cases ht0 : t = 0
        · simp [ht0]
        · obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero ht0
          have hy_xs : y ∈ xs := Multiset.mem_coe.mp (Multiset.mem_of_le hle_xs hy)
          have hyx : y ≤ x := hl.1 y hy_xs
          have ht_eq : y ::ₘ t.erase y = t := Multiset.cons_erase hy
          have herase_le : t.erase y ≤ (xs : Multiset ℕ) :=
            (Multiset.erase_le y t).trans hle_xs
          have herase_card : (t.erase y).card ≤ k' := by
            have hcard : (y ::ₘ t.erase y).card = t.card := congrArg Multiset.card ht_eq
            rw [Multiset.card_cons] at hcard
            omega
          have hih := ih hl.2 herase_le k' herase_card
          rw [← ht_eq, Multiset.sum_cons]
          omega
      · have hcard : t'.card ≤ k' := by
          rw [Multiset.card_cons] at hk
          omega
        have hih := ih hl.2 hle_xs k' hcard
        rw [Multiset.sum_cons]
        omega

/-- Every single `ExchangeStep` implies `DominatedBy`. -/
theorem exchangeStep_imp_dominatedBy {s₁ s₂ : List ℕ} (h : ExchangeStep s₁ s₂) :
    DominatedBy s₁ s₂ := by
  rcases h with ⟨hsort₁, hsort₂, m, a, b, hba, hb1, hm₁, hm₂⟩
  refine ⟨hsort₁, hsort₂, ?_, ?_, ?_⟩
  · have hc1 : s₁.length = (a ::ₘ b ::ₘ m).card := by
      rw [← Multiset.coe_card, hm₁]
    have hc2 : s₂.length = ((a + 1) ::ₘ (b - 1) ::ₘ m).card := by
      rw [← Multiset.coe_card, hm₂]
    simp only [Multiset.card_cons] at hc1 hc2
    omega
  · have hs1 : s₁.sum = (a ::ₘ b ::ₘ m).sum := by
      rw [← Multiset.sum_coe, hm₁]
    have hs2 : s₂.sum = ((a + 1) ::ₘ (b - 1) ::ₘ m).sum := by
      rw [← Multiset.sum_coe, hm₂]
    simp only [Multiset.sum_cons] at hs1 hs2
    omega
  · intro k
    set t₁ : Multiset ℕ := (s₁.take k : Multiset ℕ)
    have ht₁_le : t₁ ≤ a ::ₘ b ::ₘ m := by
      rw [← hm₁]
      exact Multiset.coe_le.mpr (List.take_sublist k s₁).subperm
    have ht₁_card : t₁.card ≤ k := by
      simp [t₁, List.length_take]
    have hsum_t₁ : (s₁.take k).sum = t₁.sum := by simp [t₁]
    rw [hsum_t₁]
    rcases multiset_le_cons_iff_cases ht₁_le with hbm | ⟨t', ht'eq, hbm⟩
    · rcases multiset_le_cons_iff_cases hbm with hm | ⟨t'', ht''eq, hm⟩
      · have hle2 : t₁ ≤ (s₂ : Multiset ℕ) := by
          rw [hm₂]
          exact hm.trans (le_trans (Multiset.le_cons_self _ _) (Multiset.le_cons_self _ _))
        exact multiset_sum_le_take_sum hsort₂ hle2 k ht₁_card
      · set t₂ : Multiset ℕ := (a + 1) ::ₘ t''
        have hle2 : t₂ ≤ (s₂ : Multiset ℕ) := by
          rw [hm₂]
          exact Multiset.cons_le_cons (a + 1) (hm.trans (Multiset.le_cons_self _ _))
        have hcard2 : t₂.card ≤ k := by
          rw [ht''eq, Multiset.card_cons] at ht₁_card
          simpa [t₂, Multiset.card_cons] using ht₁_card
        have hle_sum : t₁.sum ≤ t₂.sum := by
          rw [ht''eq]
          simp only [t₂, Multiset.sum_cons]
          omega
        exact hle_sum.trans (multiset_sum_le_take_sum hsort₂ hle2 k hcard2)
    · rcases multiset_le_cons_iff_cases hbm with hm | ⟨t'', ht''eq, hm⟩
      · set t₂ : Multiset ℕ := (a + 1) ::ₘ t'
        have hle2 : t₂ ≤ (s₂ : Multiset ℕ) := by
          rw [hm₂]
          exact Multiset.cons_le_cons (a + 1) (hm.trans (Multiset.le_cons_self _ _))
        have hcard2 : t₂.card ≤ k := by
          rw [ht'eq, Multiset.card_cons] at ht₁_card
          simpa [t₂, Multiset.card_cons] using ht₁_card
        have hle_sum : t₁.sum ≤ t₂.sum := by
          rw [ht'eq]
          simp only [t₂, Multiset.sum_cons]
          omega
        exact hle_sum.trans (multiset_sum_le_take_sum hsort₂ hle2 k hcard2)
      · set t₂ : Multiset ℕ := (a + 1) ::ₘ (b - 1) ::ₘ t''
        have hle2 : t₂ ≤ (s₂ : Multiset ℕ) := by
          rw [hm₂]
          exact Multiset.cons_le_cons (a + 1) (Multiset.cons_le_cons (b - 1) hm)
        have hcard2 : t₂.card ≤ k := by
          rw [ht'eq, ht''eq, Multiset.card_cons, Multiset.card_cons] at ht₁_card
          simpa [t₂, Multiset.card_cons] using ht₁_card
        have hle_sum : t₁.sum ≤ t₂.sum := by
          rw [ht'eq, ht''eq]
          simp only [t₂, Multiset.sum_cons]
          omega
        exact hle_sum.trans (multiset_sum_le_take_sum hsort₂ hle2 k hcard2)

/-- Any finite chain of `ExchangeStep`s implies `DominatedBy`. -/
theorem dominatedBy_of_exchangeStep_chain {s₁ s₂ : List ℕ}
    (hs₁ : s₁.Pairwise (· ≥ ·))
    (hchain : Relation.ReflTransGen ExchangeStep s₁ s₂) :
    DominatedBy s₁ s₂ := by
  induction hchain with
  | refl => exact dominatedBy_refl hs₁
  | tail _ hstep ih => exact dominatedBy_trans ih (exchangeStep_imp_dominatedBy hstep)

private lemma finset_union_val_of_disjoint {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : Disjoint s t) : (s ∪ t).val = s.val + t.val := by
  rw [← Finset.disjUnion_eq_union s t h]
  rfl

/-- Partitioning a list's underlying multiset as `M_A + M_B` yields an exact subset of indices
`S : Finset (Fin r.length)` whose values map to `M_A` and whose complement maps to `M_B`. -/
theorem exists_finset_of_multiset_add {α : Type*} [DecidableEq α] (r : List α)
    (M_A M_B : Multiset α) (h : (r : Multiset α) = M_A + M_B) :
    ∃ S : Finset (Fin r.length),
      S.val.map (fun i => r[i]) = M_A ∧
      (Finset.univ \ S).val.map (fun i => r[i]) = M_B := by
  induction r generalizing M_A M_B with
  | nil =>
    have hc : M_A.card + M_B.card = 0 := by
      have h1 := congrArg Multiset.card h
      simpa using h1.symm
    have hA0 : M_A = 0 := Multiset.card_eq_zero.mp (by omega)
    have hB0 : M_B = 0 := Multiset.card_eq_zero.mp (by omega)
    refine ⟨∅, ?_, ?_⟩
    · simp [hA0]
    · simp [hB0]
  | cons x xs ih =>
    have hx_mem : x ∈ M_A + M_B := by
      rw [← h]
      simp
    rcases Multiset.mem_add.mp hx_mem with hxA | hxB
    · have hA_eq : M_A = x ::ₘ M_A.erase x := (Multiset.cons_erase hxA).symm
      have hxs : (xs : Multiset α) = M_A.erase x + M_B := by
        have h' : x ::ₘ (xs : Multiset α) = x ::ₘ (M_A.erase x + M_B) := by
          rw [← Multiset.cons_add, ← hA_eq]
          simpa using h
        exact (Multiset.cons_inj_right x).mp h'
      obtain ⟨S', hS'A, hS'B⟩ := ih (M_A.erase x) M_B hxs
      let S : Finset (Fin (xs.length + 1)) := insert 0 (S'.map (Fin.succEmb xs.length))
      have h0_not : (0 : Fin (xs.length + 1)) ∉ S'.map (Fin.succEmb xs.length) := by
        simp [Fin.succEmb]
      have hcompl : Finset.univ \ S = (Finset.univ \ S').map (Fin.succEmb xs.length) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [S]
        · intro j
          simp [S, Fin.succEmb]
      refine ⟨S, ?_, ?_⟩
      · have hval : S.val = (0 : Fin (xs.length + 1)) ::ₘ (S'.map (Fin.succEmb xs.length)).val :=
          Finset.insert_val_of_notMem h0_not
        rw [hval, Multiset.map_cons, Finset.map_val, Multiset.map_map, hA_eq, ← hS'A]
        congr 1
      · rw [hcompl, Finset.map_val, Multiset.map_map, ← hS'B]
        exact Multiset.map_congr rfl (fun _ _ => rfl)
    · have hB_eq : M_B = x ::ₘ M_B.erase x := (Multiset.cons_erase hxB).symm
      have hxs : (xs : Multiset α) = M_A + M_B.erase x := by
        have h' : x ::ₘ (xs : Multiset α) = x ::ₘ (M_A + M_B.erase x) := by
          rw [← Multiset.add_cons, ← hB_eq]
          simpa using h
        exact (Multiset.cons_inj_right x).mp h'
      obtain ⟨S', hS'A, hS'B⟩ := ih M_A (M_B.erase x) hxs
      let S : Finset (Fin (xs.length + 1)) := S'.map (Fin.succEmb xs.length)
      have h0_not : (0 : Fin (xs.length + 1)) ∉ (Finset.univ \ S').map (Fin.succEmb xs.length) := by
        simp [Fin.succEmb]
      have hcompl : Finset.univ \ S = insert 0 ((Finset.univ \ S').map (Fin.succEmb xs.length)) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [S, Fin.succEmb]
        · intro j
          simp [S, Fin.succEmb]
      refine ⟨S, ?_, ?_⟩
      · rw [Finset.map_val, Multiset.map_map, ← hS'A]
        exact Multiset.map_congr rfl (fun _ _ => rfl)
      · have hval : (Finset.univ \ S).val =
            (0 : Fin (xs.length + 1)) ::ₘ ((Finset.univ \ S').map (Fin.succEmb xs.length)).val := by
          rw [hcompl]
          exact Finset.insert_val_of_notMem h0_not
        rw [hval, Multiset.map_cons, Finset.map_val, Multiset.map_map, hB_eq, ← hS'B]
        congr 1

/-- `(List.finRange m : Multiset (Fin m))` equals `(Finset.univ : Finset (Fin m)).val`. -/
theorem finRange_coe_eq_univ_val (m : ℕ) :
    ((List.finRange m : List (Fin m)) : Multiset (Fin m)) = (Finset.univ : Finset (Fin m)).val := by
  have hnodup : ((List.finRange m : List (Fin m)) : Multiset (Fin m)).Nodup :=
    Multiset.coe_nodup.mpr (List.nodup_finRange m)
  exact (Multiset.Nodup.ext hnodup Finset.univ.nodup).mpr (fun i => by simp)

/-- Sorted list obtained from `r` by decrementing entries at indices in `S`. -/
def decrementedMultiset (r : List ℕ) (S : Finset (Fin r.length)) : Multiset ℕ :=
  (Finset.univ : Finset (Fin r.length)).val.map (fun i => if i ∈ S then r[i] - 1 else r[i])

/-- Descending sorted list obtained from `r` by decrementing entries at indices in `S`. -/
def decrementedSort (r : List ℕ) (S : Finset (Fin r.length)) : List ℕ :=
  (decrementedMultiset r S).sort (· ≥ ·)

theorem decrementedSort_eq_mergeSort_finRange (r : List ℕ) (S : Finset (Fin r.length)) :
    decrementedSort r S =
      ((List.finRange r.length).map (fun i => if i ∈ S then r[i] - 1 else r[i])).mergeSort
        (· ≥ ·) := by
  rw [mergeSort_ge_eq_sort]
  unfold decrementedSort decrementedMultiset
  rw [← finRange_coe_eq_univ_val, Multiset.map_coe]

theorem decrementedMultiset_eq_add (r : List ℕ) (S : Finset (Fin r.length)) :
    decrementedMultiset r S =
      (S.val.map (fun i => r[i])).map (· - 1) + (Finset.univ \ S).val.map (fun i => r[i]) := by
  unfold decrementedMultiset
  have huniv : (Finset.univ : Finset (Fin r.length)).val = S.val + (Finset.univ \ S).val := by
    have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
    have hunion : S ∪ (Finset.univ \ S) = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    calc
      (Finset.univ : Finset (Fin r.length)).val = (S ∪ (Finset.univ \ S)).val :=
        congrArg Finset.val hunion.symm
      _ = S.val + (Finset.univ \ S).val := finset_union_val_of_disjoint hdisj
  rw [huniv, Multiset.map_add, Multiset.map_map]
  congr 1
  · apply Multiset.map_congr rfl
    intro i hi
    simp [Finset.mem_def.mpr hi]
  · apply Multiset.map_congr rfl
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp (Finset.mem_def.mpr hi)).2
    simp [hnot]

/-- Top-`d` index set in `Fin r.length`. -/
def topFinset (m d : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i : Fin m => i.1 < d)

theorem card_topFinset {m d : ℕ} (hd : d ≤ m) : (topFinset m d).card = d := by
  have heq : topFinset m d =
      (Finset.univ : Finset (Fin d)).map ⟨fun j => ⟨j.1, lt_of_lt_of_le j.2 hd⟩, by
        intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext i
    simp only [topFinset, mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hi
      exact ⟨⟨i.1, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  rw [heq, card_map, card_fin]

private lemma list_take_coe_eq_topFinset_map (r : List ℕ) (d : ℕ) :
    (r.take d : Multiset ℕ) = (topFinset r.length d).val.map (fun i => r[i]) := by
  induction r generalizing d with
  | nil => simp [topFinset]
  | cons x xs ih =>
    cases d with
    | zero =>
      simp [topFinset]
    | succ d' =>
      have htop : topFinset (xs.length + 1) (d' + 1) =
          insert 0 ((topFinset xs.length d').map (Fin.succEmb xs.length)) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [topFinset]
        · intro j
          simp [topFinset, Fin.succEmb]
      have h0_not : (0 : Fin (xs.length + 1)) ∉ (topFinset xs.length d').map (Fin.succEmb xs.length) := by
        simp [Fin.succEmb]
      have hval : (topFinset (xs.length + 1) (d' + 1)).val =
          (0 : Fin (xs.length + 1)) ::ₘ ((topFinset xs.length d').map (Fin.succEmb xs.length)).val := by
        rw [htop]
        exact Finset.insert_val_of_notMem h0_not
      simp only [List.take_succ_cons, List.length_cons]
      rw [hval, Multiset.map_cons, Finset.map_val, Multiset.map_map]
      have hcomp : ((fun i : Fin (xs.length + 1) => (x :: xs)[i]) ∘ ⇑(Fin.succEmb xs.length)) =
          (fun j : Fin xs.length => xs[j]) := by
        funext j
        rfl
      rw [hcomp, ← ih d']
      rfl

private lemma list_drop_coe_eq_compl_topFinset_map (r : List ℕ) (d : ℕ) :
    (r.drop d : Multiset ℕ) = (Finset.univ \ topFinset r.length d).val.map (fun i => r[i]) := by
  have h1 : (r : Multiset ℕ) = (r.take d : Multiset ℕ) + (r.drop d : Multiset ℕ) := by
    rw [Multiset.coe_add, List.take_append_drop]
  have h2 : (r : Multiset ℕ) = (Finset.univ : Finset (Fin r.length)).val.map (fun i => r[i]) := by
    rw [← finRange_coe_eq_univ_val, Multiset.map_coe]
    congr 1
    exact (List.map_getElem_finRange r).symm
  have h3 : (Finset.univ : Finset (Fin r.length)).val =
      (topFinset r.length d).val + (Finset.univ \ topFinset r.length d).val := by
    have hdisj : Disjoint (topFinset r.length d) (Finset.univ \ topFinset r.length d) :=
      disjoint_sdiff_self_right
    have hunion : topFinset r.length d ∪ (Finset.univ \ topFinset r.length d) = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ _)
    calc
      (Finset.univ : Finset (Fin r.length)).val
          = (topFinset r.length d ∪ (Finset.univ \ topFinset r.length d)).val :=
            congrArg Finset.val hunion.symm
      _ = (topFinset r.length d).val + (Finset.univ \ topFinset r.length d).val :=
            finset_union_val_of_disjoint hdisj
  rw [h3, Multiset.map_add, ← list_take_coe_eq_topFinset_map] at h2
  have hsum : (r.take d : Multiset ℕ) + (r.drop d : Multiset ℕ) =
      (r.take d : Multiset ℕ) + (Finset.univ \ topFinset r.length d).val.map (fun i => r[i]) :=
    h1.symm.trans h2
  exact add_left_cancel hsum

/-- `havelHakimiStep (d :: r)` equals `decrementedSort r (topFinset r.length d)`. -/
theorem havelHakimiStep_eq_decrementedSort_topFinset (d : ℕ) (r : List ℕ) :
    SimpleGraph.havelHakimiStep (d :: r) = decrementedSort r (topFinset r.length d) := by
  rw [havelHakimiStep_eq_sort]
  unfold decrementedSort
  rw [decrementedMultiset_eq_add, ← list_take_coe_eq_topFinset_map,
    ← list_drop_coe_eq_compl_topFinset_map]
  rfl

/-- Swapping one index `i ∈ U` out and one index `j ∉ U` in either leaves `decrementedSort`
unchanged (if `r[i] = r[j]`) or performs one `ExchangeStep` (if `r[j] < r[i]`). -/
private lemma decrementedSort_swap_step (r : List ℕ) (U : Finset (Fin r.length))
    {i j : Fin r.length} (hi : i ∈ U) (hj : j ∉ U)
    (hle : r[j] ≤ r[i]) (hj1 : 1 ≤ r[j]) :
    let U' := insert j (U.erase i)
    decrementedSort r U = decrementedSort r U' ∨
      ExchangeStep (decrementedSort r U) (decrementedSort r U') := by
  intro U'
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  let R : Finset (Fin r.length) := (Finset.univ.erase i).erase j
  have hi_not_R : i ∉ R := by simp [R]
  have hj_not_R : j ∉ R := by simp [R]
  have hj_mem_erase_i : j ∈ (Finset.univ : Finset (Fin r.length)).erase i :=
    mem_erase.mpr ⟨hij.symm, mem_univ j⟩
  have huniv_val : (Finset.univ : Finset (Fin r.length)).val = i ::ₘ j ::ₘ R.val := by
    have h1 : (Finset.univ : Finset (Fin r.length)) = insert i (insert j R) := by
      ext k
      simp only [R, mem_univ, mem_insert, mem_erase, and_true, true_iff]
      by_cases hki : k = i
      · exact Or.inl hki
      · by_cases hkj : k = j
        · exact Or.inr (Or.inl hkj)
        · exact Or.inr (Or.inr ⟨hkj, hki⟩)
    have h2 : i ∉ insert j R := by simp [R, hij]
    rw [h1, Finset.insert_val_of_notMem h2, Finset.insert_val_of_notMem hj_not_R]
  have hagree : ∀ k ∈ R.val,
      (if k ∈ U then r[k] - 1 else r[k]) = (if k ∈ U' then r[k] - 1 else r[k]) := by
    intro k hk
    have hk' := Finset.mem_def.mpr hk
    have hkj : k ≠ j := (mem_erase.mp hk').1
    have hki : k ≠ i := (mem_erase.mp (mem_erase.mp hk').2).1
    have hiff : k ∈ U' ↔ k ∈ U := by
      simp [U', hkj, hki]
    simp [hiff]
  let m : Multiset ℕ := R.val.map (fun k => if k ∈ U then r[k] - 1 else r[k])
  have hU_mul : decrementedMultiset r U = (r[i] - 1) ::ₘ r[j] ::ₘ m := by
    unfold decrementedMultiset
    rw [huniv_val, Multiset.map_cons, Multiset.map_cons]
    simp [hi, hj, m]
  have hi_not_U' : i ∉ U' := by simp [U', hij]
  have hj_mem_U' : j ∈ U' := by simp [U']
  have hU'_mul : decrementedMultiset r U' = r[i] ::ₘ (r[j] - 1) ::ₘ m := by
    unfold decrementedMultiset
    rw [huniv_val, Multiset.map_cons, Multiset.map_cons]
    simp only [hi_not_U', hj_mem_U', ↓reduceIte]
    congr 2
    exact (Multiset.map_congr rfl hagree).symm
  rcases eq_or_lt_of_le hle with heq | hlt
  · left
    unfold decrementedSort
    rw [hU_mul, hU'_mul, heq, Multiset.cons_swap]
  · right
    refine ⟨Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _,
      m, r[i] - 1, r[j], by omega, hj1, ?_, ?_⟩
    · unfold decrementedSort
      rw [Multiset.sort_eq, hU_mul]
    · unfold decrementedSort
      rw [Multiset.sort_eq, hU'_mul]
      have hri : r[i] - 1 + 1 = r[i] := by omega
      rw [hri]

/-- **Core Sorted-List Decrement Bridge:**
For any descending list `r` and any `d`-element subset `S` of indices with `∀ j ∈ S, 1 ≤ r[j]`,
there is a finite chain of `ExchangeStep`s from `havelHakimiStep (d :: r)` (which decrements the
`d` largest entries of `r`) up to `decrementedSort r S` (which decrements the entries in `S`). -/
theorem exchangeStep_chain_of_subset_decrement {d : ℕ} {r : List ℕ}
    (hr : r.Pairwise (· ≥ ·)) (S : Finset (Fin r.length))
    (hcard : S.card = d) (hpos : ∀ j ∈ S, 1 ≤ r[j]) :
    Relation.ReflTransGen ExchangeStep
      (SimpleGraph.havelHakimiStep (d :: r)) (decrementedSort r S) := by
  have hd_le : d ≤ r.length := by
    rw [← hcard]
    exact (Finset.card_le_univ S).trans (by simp)
  rw [havelHakimiStep_eq_decrementedSort_topFinset]
  have aux : ∀ (k : ℕ) (U : Finset (Fin r.length)),
      U.card = d →
      (U \ S).card = k →
      (∀ i ∈ U \ S, i.1 < d) →
      (∀ j ∈ S \ U, d ≤ j.1) →
      Relation.ReflTransGen ExchangeStep (decrementedSort r U) (decrementedSort r S) := by
    intro k
    induction k with
    | zero =>
      intro U hUcard hdiff0 _ _
      have hU_sub : U ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hdiff0)
      have hUS : U = S := Finset.eq_of_subset_of_card_le hU_sub (by omega)
      subst hUS
      exact Relation.ReflTransGen.refl
    | succ k' ih =>
      intro U hUcard hdiff hlt hge
      have hUS_ne : (U \ S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i, hi⟩ := hUS_ne
      have hSU_card : (S \ U).card = k' + 1 := by
        have h1 := Finset.card_sdiff_add_card_inter U S
        have h2 := Finset.card_sdiff_add_card_inter S U
        rw [Finset.inter_comm] at h2
        omega
      have hSU_ne : (S \ U).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, hj⟩ := hSU_ne
      have hiU : i ∈ U := (mem_sdiff.mp hi).1
      have hi_not_S : i ∉ S := (mem_sdiff.mp hi).2
      have hjS : j ∈ S := (mem_sdiff.mp hj).1
      have hj_not_U : j ∉ U := (mem_sdiff.mp hj).2
      have hij_lt : i.1 < d := hlt i hi
      have hdj_le : d ≤ j.1 := hge j hj
      have hle : r[j] ≤ r[i] := pairwise_ge_getElem_le hr i.2 j.2 (by omega)
      have hj1 : 1 ≤ r[j] := hpos j hjS
      let U' : Finset (Fin r.length) := insert j (U.erase i)
      have hj_not_erase : j ∉ U.erase i := fun h => hj_not_U (mem_of_mem_erase h)
      have hU'card : U'.card = d := by
        rw [card_insert_of_notMem hj_not_erase, card_erase_add_one hiU, hUcard]
      have hU'diff : U' \ S = (U \ S).erase i := by
        ext x
        simp only [U', mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hxi, hxU⟩, hxS⟩
          · exact absurd hjS hxS
          · exact ⟨hxi, hxU, hxS⟩
        · rintro ⟨hxi, hxU, hxS⟩
          exact ⟨Or.inr ⟨hxi, hxU⟩, hxS⟩
      have hSU'diff : S \ U' = (S \ U).erase j := by
        ext x
        simp only [U', mem_sdiff, mem_insert, mem_erase, not_or, not_and]
        constructor
        · rintro ⟨hxS, hxj, hnot⟩
          refine ⟨hxj, hxS, ?_⟩
          intro hxU
          have hxi : x ≠ i := fun h => hi_not_S (h ▸ hxS)
          exact hnot hxi hxU
        · rintro ⟨hxj, hxS, hxU⟩
          exact ⟨hxS, hxj, fun _ h => hxU h⟩
      have hU'diff_card : (U' \ S).card = k' := by
        rw [hU'diff, card_erase_of_mem hi, hdiff]
        omega
      have hlt' : ∀ x ∈ U' \ S, x.1 < d := by
        intro x hx
        rw [hU'diff] at hx
        exact hlt x (mem_of_mem_erase hx)
      have hge' : ∀ x ∈ S \ U', d ≤ x.1 := by
        intro x hx
        rw [hSU'diff] at hx
        exact hge x (mem_of_mem_erase hx)
      have htail := ih U' hU'card hU'diff_card hlt' hge'
      rcases decrementedSort_swap_step r U hiU hj_not_U hle hj1 with heq | hstep
      · rwa [heq]
      · exact Relation.ReflTransGen.head hstep htail
  refine aux (topFinset r.length d \ S).card (topFinset r.length d)
    (card_topFinset hd_le) rfl ?_ ?_
  · intro i hi
    exact (mem_filter.mp (mem_sdiff.mp hi).1).2
  · intro j hj
    have hnot : j ∉ topFinset r.length d := (mem_sdiff.mp hj).2
    simp only [topFinset, mem_filter, mem_univ, true_and, not_lt] at hnot
    exact hnot

/-- Corollaries for `DominatedBy`: `havelHakimiStep (d :: r)` is dominated by `decrementedSort r S`. -/
theorem dominatedBy_of_subset_decrement {d : ℕ} {r : List ℕ}
    (hr : r.Pairwise (· ≥ ·)) (S : Finset (Fin r.length))
    (hcard : S.card = d) (hpos : ∀ j ∈ S, 1 ≤ r[j]) :
    DominatedBy (SimpleGraph.havelHakimiStep (d :: r)) (decrementedSort r S) :=
  dominatedBy_of_exchangeStep_chain (havelHakimiStep_pairwise _)
    (exchangeStep_chain_of_subset_decrement hr S hcard hpos)

end ListMultisetHelpers

/-! ## 3. Degree Multisets, Descending Degree Lists, and Induced Vertex Deletion -/

section GraphDegreeLists

/-- The multiset of vertex degrees of a finite simple graph `G`. -/
def degMultiset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map (fun v => G.degree v)

/-- The descending sorted degree sequence of a finite simple graph `G`. -/
def degList {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (degMultiset G).sort (· ≥ ·)

/-- The multiset of degrees in `G` of all vertices other than `v`. -/
def restMultiset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Multiset ℕ :=
  (Finset.univ.erase v).val.map (fun u => G.degree u)

/-- The descending sorted list of degrees in `G` of all vertices other than `v`. -/
def restList {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : List ℕ :=
  (restMultiset G v).sort (· ≥ ·)

/-- A `List ℕ` is graphic if it is the descending degree sequence of some finite simple graph
on `Fin n`. -/
def IsGraphic (s : List ℕ) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), degList G = s

theorem degList_pairwise {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degList G).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem restList_pairwise {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (restList G v).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem degList_coe {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((degList G : List ℕ) : Multiset ℕ) = degMultiset G :=
  Multiset.sort_eq _ _

theorem restList_coe {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((restList G v : List ℕ) : Multiset ℕ) = restMultiset G v :=
  Multiset.sort_eq _ _

theorem degList_length {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degList G).length = Fintype.card V := by
  simp [degList, degMultiset, Multiset.length_sort]

theorem isGraphic_pairwise {s : List ℕ} (hs : IsGraphic s) : s.Pairwise (· ≥ ·) := by
  rcases hs with ⟨n, G, _, rfl⟩
  exact degList_pairwise G

/-- `SimpleGraph.residue G` is definitionally `SimpleGraph.residueAux (degList G)`. -/
theorem residue_eq_residueAux_degList {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph.residue G = SimpleGraph.residueAux (degList G) :=
  rfl

/-- Graph isomorphisms preserve `degMultiset` and `degList`. -/
theorem degMultiset_eq_of_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : degMultiset G = degMultiset H := by
  unfold degMultiset
  have hdeg : ∀ v : V, H.degree (e v) = G.degree v := by
    intro v
    have hnb : H.neighborFinset (e v) = (G.neighborFinset v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, mem_map, Equiv.toEmbedding_apply]
      constructor
      · intro hw
        refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
        have : H.Adj (e v) (e (e.symm w)) := by simpa using hw
        exact e.map_rel_iff.mp this
      · rintro ⟨u, hu, rfl⟩
        exact e.map_rel_iff.mpr hu
    simp only [SimpleGraph.degree, hnb, card_map]
  have huniv : Finset.univ.map e.toEquiv.toEmbedding = (Finset.univ : Finset W) := by
    ext w
    simp only [mem_map, mem_univ, true_and, Equiv.toEmbedding_apply, iff_true]
    exact ⟨e.symm w, e.apply_symm_apply w⟩
  have hval : (Finset.univ : Finset W).val = (Finset.univ : Finset V).val.map e.toEquiv := by
    rw [← huniv, Finset.map_val]
    rfl
  rw [hval, Multiset.map_map]
  congr 1
  funext v
  exact (hdeg v).symm

theorem degList_eq_of_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : degList G = degList H := by
  unfold degList
  rw [degMultiset_eq_of_iso e]

/-- Every finite simple graph on any finite type `V` has a graphic degree list. -/
theorem isGraphic_of_degList {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsGraphic (degList G) := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let G_fin : SimpleGraph (Fin (Fintype.card V)) := G.comap e.symm
  let inst : DecidableRel G_fin.Adj := fun a b =>
    decidable_of_iff (G.Adj (e.symm a) (e.symm b)) Iff.rfl
  let iso : G ≃g G_fin :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        change G.Adj (e.symm (e a)) (e.symm (e b)) ↔ G.Adj a b
        simp }
  exact ⟨Fintype.card V, G_fin, inst, (degList_eq_of_iso iso).symm⟩

/-- If `v` has maximum degree in `Q`, then `degList Q = Q.degree v :: restList Q v`. -/
theorem degList_eq_cons_of_max {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V)
    (hmax : ∀ u, Q.degree u ≤ Q.degree v) :
    degList Q = Q.degree v :: restList Q v := by
  unfold degList restList degMultiset restMultiset
  have hv_mem : v ∈ (Finset.univ : Finset V) := mem_univ v
  have huniv : (Finset.univ : Finset V).val = v ::ₘ (Finset.univ.erase v).val := by
    calc
      (Finset.univ : Finset V).val = (insert v (Finset.univ.erase v)).val :=
        congrArg Finset.val (insert_erase hv_mem).symm
      _ = v ::ₘ (Finset.univ.erase v).val := Finset.insert_val_of_notMem (notMem_erase v _)
  rw [huniv, Multiset.map_cons]
  apply Multiset.sort_cons (r := (· ≥ ·))
  intro d hd
  rcases Multiset.mem_map.mp hd with ⟨u, _, rfl⟩
  exact hmax u

/-- For any maximum-degree vertex `v` with positive degree, `SimpleGraph.residue Q`
equals `SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v))`. -/
theorem residue_eq_residueAux_hhStep_of_max {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V)
    (hmax : ∀ u, Q.degree u ≤ Q.degree v) (hpos : 0 < Q.degree v) :
    SimpleGraph.residue Q =
      SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v)) := by
  rw [residue_eq_residueAux_degList, degList_eq_cons_of_max Q v hmax,
    residueAux_cons_of_pos hpos]

/-- Pointwise degree formula in the vertex-deleted induced subgraph `Q - v`. -/
theorem induce_ne_degree {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) (u : { z : V // z ≠ v }) :
    (Q.induce { z : V | z ≠ v }).degree u =
      if Q.Adj v u.1 then Q.degree u.1 - 1 else Q.degree u.1 := by
  have hmap : ((Q.induce { z : V | z ≠ v }).neighborFinset u).map
      ⟨Subtype.val, Subtype.val_injective⟩ = (Q.neighborFinset u.1).erase v := by
    ext w
    simp only [mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk,
      mem_erase, SimpleGraph.induce_adj]
    constructor
    · rintro ⟨⟨z, hz⟩, hadj, rfl⟩
      exact ⟨hz, hadj⟩
    · rintro ⟨hwv, hadj⟩
      exact ⟨⟨w, hwv⟩, hadj, rfl⟩
  have hcard : (Q.induce { z : V | z ≠ v }).degree u = ((Q.neighborFinset u.1).erase v).card := by
    rw [SimpleGraph.degree, ← card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap]
  rw [hcard]
  by_cases hadj : Q.Adj v u.1
  · have hv_mem : v ∈ Q.neighborFinset u.1 := (Q.mem_neighborFinset u.1 v).mpr hadj.symm
    rw [ite_eq_left hadj, card_erase_of_mem hv_mem, SimpleGraph.degree]
  · have hv_not : v ∉ Q.neighborFinset u.1 := by
      rw [Q.mem_neighborFinset]
      exact fun h => hadj h.symm
    rw [ite_eq_right hadj, erase_eq_of_notMem hv_not, SimpleGraph.degree]

/-- **Exact Degree Multiset Partition for Induced Vertex Deletion `Q - v`:**
Splitting `V \ {v}` into `N_Q(v)` and `(V \ {v}) \ N_Q(v)` partitions `restMultiset Q v` as
`M_A + M_B` with `M_A.card = Q.degree v` and `∀ x ∈ M_A, 1 ≤ x`, such that
`degMultiset (Q - v) = M_A.map (· - 1) + M_B`. -/
theorem induce_ne_degMultiset_partition {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    ∃ M_A M_B : Multiset ℕ,
      restMultiset Q v = M_A + M_B ∧
      degMultiset (Q.induce { u : V | u ≠ v }) = M_A.map (· - 1) + M_B ∧
      M_A.card = Q.degree v ∧
      ∀ x ∈ M_A, 1 ≤ x := by
  let Nv : Finset V := Q.neighborFinset v
  let Bv : Finset V := (Finset.univ.erase v) \ Nv
  have hNv_sub : Nv ⊆ Finset.univ.erase v := by
    intro u hu
    exact mem_erase.mpr ⟨((Q.mem_neighborFinset v u).mp hu).ne.symm, mem_univ u⟩
  have hdisj : Disjoint Nv Bv := disjoint_sdiff_self_right
  have hunion : Nv ∪ Bv = Finset.univ.erase v := union_sdiff_of_subset hNv_sub
  have herase_val : (Finset.univ.erase v).val = Nv.val + Bv.val := by
    rw [← hunion, finset_union_val_of_disjoint hdisj]
  let M_A : Multiset ℕ := Nv.val.map (fun u => Q.degree u)
  let M_B : Multiset ℕ := Bv.val.map (fun u => Q.degree u)
  refine ⟨M_A, M_B, ?_, ?_, ?_, ?_⟩
  · unfold restMultiset
    rw [herase_val, Multiset.map_add]
  · -- Relate `degMultiset (Q.induce {u | u ≠ v})` to `(univ.erase v).val.map ...`.
    let emb : { u : V // u ≠ v } ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    have huniv_map : (Finset.univ : Finset { u : V // u ≠ v }).map emb = Finset.univ.erase v := by
      ext u
      simp only [mem_map, mem_univ, true_and, mem_erase, and_true, emb, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩; exact hz
      · intro huv; exact ⟨⟨u, huv⟩, rfl⟩
    have hval_sub : (Finset.univ.erase v).val =
        (Finset.univ : Finset { u : V // u ≠ v }).val.map Subtype.val := by
      rw [← huniv_map, Finset.map_val]
      rfl
    have hdeg_ind : degMultiset (Q.induce { u : V | u ≠ v }) =
        (Finset.univ.erase v).val.map (fun u => if Q.Adj v u then Q.degree u - 1 else Q.degree u) := by
      unfold degMultiset
      rw [hval_sub, Multiset.map_map]
      congr 1
      funext u
      exact induce_ne_degree Q v u
    rw [hdeg_ind, herase_val, Multiset.map_add]
    congr 1
    · rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro u hu
      have hadj : Q.Adj v u := (Q.mem_neighborFinset v u).mp (Finset.mem_def.mpr hu)
      simp [hadj]
    · apply Multiset.map_congr rfl
      intro u hu
      have hnot : u ∉ Nv := (mem_sdiff.mp (Finset.mem_def.mpr hu)).2
      have hnot_adj : ¬ Q.Adj v u := fun h => hnot ((Q.mem_neighborFinset v u).mpr h)
      simp [hnot_adj]
  · change (Nv.val.map (fun u => Q.degree u)).card = Q.degree v
    rw [Multiset.card_map]
    exact Q.card_neighborFinset_eq_degree v
  · intro x hx
    rcases Multiset.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hadj : Q.Adj u v := ((Q.mem_neighborFinset v u).mp (Finset.mem_def.mpr hu)).symm
    exact Finset.card_pos.mpr ⟨v, (Q.mem_neighborFinset u v).mpr hadj⟩

/-- **Indexed Decrement Representation for Induced Vertex Deletion `Q - v`:**
There exists an index subset `S : Finset (Fin (restList Q v).length)` of cardinality
`Q.degree v` with `∀ i ∈ S, 1 ≤ (restList Q v)[i]` such that `degList (Q - v)` equals
`decrementedSort (restList Q v) S` (equivalently `((List.finRange _).map ...).mergeSort (· ≥ ·)`). -/
theorem induce_ne_degList_as_indexed_decrement {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    ∃ S : Finset (Fin (restList Q v).length),
      S.card = Q.degree v ∧
      (∀ i ∈ S, 1 ≤ (restList Q v)[i]) ∧
      degList (Q.induce { u : V | u ≠ v }) = decrementedSort (restList Q v) S := by
  obtain ⟨M_A, M_B, hrest, hdel, hcard, hpos⟩ := induce_ne_degMultiset_partition Q v
  have hcoe : ((restList Q v : List ℕ) : Multiset ℕ) = M_A + M_B := by
    rw [restList_coe, hrest]
  obtain ⟨S, hSA, hSB⟩ := exists_finset_of_multiset_add (restList Q v) M_A M_B hcoe
  refine ⟨S, ?_, ?_, ?_⟩
  · have hc : S.card = M_A.card := by
      rw [← hSA, Multiset.card_map]
      rfl
    omega
  · intro i hi
    apply hpos
    rw [← hSA]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_def.mp hi, rfl⟩
  · unfold degList decrementedSort
    rw [hdel, decrementedMultiset_eq_add, hSA, hSB]

/-- **Unconditional Exchange Chain for Max-Degree Vertex Deletion:**
Deleting a maximum-degree vertex `v` yields a degree list `degList (Q - v)` reachable from
`havelHakimiStep (Q.degree v :: restList Q v)` by a finite chain of `ExchangeStep`s. -/
theorem exchangeStep_chain_of_maxDegDeletion {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    Relation.ReflTransGen ExchangeStep
      (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v))
      (degList (Q.induce { u : V | u ≠ v })) := by
  obtain ⟨S, hcard, hpos, hdeg⟩ := induce_ne_degList_as_indexed_decrement Q v
  rw [hdeg]
  exact exchangeStep_chain_of_subset_decrement (restList_pairwise Q v) S hcard hpos

/-- **Unconditional Dominance for Max-Degree Vertex Deletion:**
`havelHakimiStep (Q.degree v :: restList Q v)` is dominated by `degList (Q - v)`. -/
theorem dominatedBy_of_maxDegDeletion {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    DominatedBy
      (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v))
      (degList (Q.induce { u : V | u ≠ v })) :=
  dominatedBy_of_exchangeStep_chain (havelHakimiStep_pairwise _)
    (exchangeStep_chain_of_maxDegDeletion Q v)

end GraphDegreeLists

/-! ## 4. Local Edge Shift (`edgeShift`) and Classical Havel–Hakimi Theorem -/

section HavelHakimiClosure

/-- Single-edge shift: delete edge `{u, w}` and add edge `{v, w}`. -/
def edgeShift {V : Type*} (G : SimpleGraph V) (u v w : V) : SimpleGraph V :=
  (G.deleteEdges {s(u, w)}) ⊔ SimpleGraph.fromEdgeSet {s(v, w)}

instance instDecidableRelEdgeShift {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V) :
    DecidableRel (edgeShift G u v w).Adj := fun a b =>
  decidable_of_iff
    ((G.Adj a b ∧ s(a, b) ≠ s(u, w)) ∨ (s(a, b) = s(v, w) ∧ a ≠ b))
    (by simp [edgeShift, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
      SimpleGraph.fromEdgeSet_adj])

theorem edgeShift_adj_iff {V : Type*} (G : SimpleGraph V) {u v w : V} (hne_vw : v ≠ w) (a b : V) :
    (edgeShift G u v w).Adj a b ↔ (G.Adj a b ∧ s(a, b) ≠ s(u, w)) ∨ s(a, b) = s(v, w) := by
  simp only [edgeShift, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      intro hab
      subst hab
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne_vw rfl

theorem edgeShift_neighborFinset_u {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huw : G.Adj u w) (huv : u ≠ v) (hvw : v ≠ w) :
    (edgeShift G u v w).neighborFinset u = (G.neighborFinset u).erase w := by
  have huw_ne : u ≠ w := huw.ne
  ext z
  simp only [SimpleGraph.mem_neighborFinset, edgeShift_adj_iff G hvw, mem_erase, Sym2.eq_iff,
    ne_eq, true_and]
  constructor
  · rintro (⟨hz, hne⟩ | (⟨h, _⟩ | ⟨h, _⟩))
    · exact ⟨fun hzw => hne (Or.inl hzw), hz⟩
    · exact absurd h huv
    · exact absurd h huw_ne
  · rintro ⟨hzw, hz⟩
    refine Or.inl ⟨hz, ?_⟩
    rintro (h | ⟨h, _⟩)
    · exact hzw h
    · exact huw_ne h

theorem edgeShift_neighborFinset_v {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huw : G.Adj u w) (huv : u ≠ v) (hvw : v ≠ w) :
    (edgeShift G u v w).neighborFinset v = insert w (G.neighborFinset v) := by
  ext z
  simp only [SimpleGraph.mem_neighborFinset, edgeShift_adj_iff G hvw, mem_insert, Sym2.eq_iff,
    ne_eq, true_and]
  constructor
  · rintro (⟨hz, _⟩ | (rfl | ⟨h, _⟩))
    · exact Or.inr hz
    · exact Or.inl rfl
    · exact absurd h hvw
  · rintro (rfl | hz)
    · exact Or.inr (Or.inl rfl)
    · refine Or.inl ⟨hz, ?_⟩
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact huv.symm h
      · exact hvw h

theorem edgeShift_neighborFinset_w {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huw : G.Adj u w) (hvw : v ≠ w) :
    (edgeShift G u v w).neighborFinset w = insert v ((G.neighborFinset w).erase u) := by
  have huw_ne : u ≠ w := huw.ne
  ext z
  simp only [SimpleGraph.mem_neighborFinset, edgeShift_adj_iff G hvw, mem_insert, mem_erase,
    Sym2.eq_iff, ne_eq, true_and]
  constructor
  · rintro (⟨hz, hne⟩ | (⟨h, _⟩ | rfl))
    · exact Or.inr ⟨fun hzu => hne (Or.inr hzu), hz⟩
    · exact absurd h hvw.symm
    · exact Or.inl rfl
  · rintro (rfl | ⟨hzu, hz⟩)
    · exact Or.inr (Or.inr rfl)
    · refine Or.inl ⟨hz, ?_⟩
      rintro (⟨h, _⟩ | h)
      · exact huw_ne.symm h
      · exact hzu h

theorem edgeShift_neighborFinset_other {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w z : V}
    (hvw : v ≠ w) (hzu : z ≠ u) (hzv : z ≠ v) (hzw : z ≠ w) :
    (edgeShift G u v w).neighborFinset z = G.neighborFinset z := by
  ext x
  simp only [SimpleGraph.mem_neighborFinset, edgeShift_adj_iff G hvw, Sym2.eq_iff, ne_eq]
  constructor
  · rintro (⟨hx, _⟩ | (⟨h, _⟩ | ⟨h, _⟩))
    · exact hx
    · exact absurd h hzv
    · exact absurd h hzw
  · intro hx
    refine Or.inl ⟨hx, ?_⟩
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hzu h
    · exact hzw h

/-- Pointwise degree update of `edgeShift G u v w`: decreases `deg u` by 1, increases `deg v` by 1,
and preserves every other vertex's degree (including `w`). -/
theorem edgeShift_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huw : G.Adj u w) (hnot_vw : ¬ G.Adj v w) (huv : u ≠ v) (hvw : v ≠ w) :
    (edgeShift G u v w).degree u = G.degree u - 1 ∧
    (edgeShift G u v w).degree v = G.degree v + 1 ∧
    (∀ z : V, z ≠ u → z ≠ v → (edgeShift G u v w).degree z = G.degree z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.degree, edgeShift_neighborFinset_u G huw huv hvw,
      card_erase_of_mem ((G.mem_neighborFinset u w).mpr huw), SimpleGraph.degree]
  · have hw_not : w ∉ G.neighborFinset v := fun h => hnot_vw ((G.mem_neighborFinset v w).mp h)
    rw [SimpleGraph.degree, edgeShift_neighborFinset_v G huw huv hvw,
      card_insert_of_notMem hw_not, SimpleGraph.degree]
  · intro z hzu hzv
    by_cases hzw : z = w
    · subst hzw
      have hu_mem : u ∈ G.neighborFinset z := (G.mem_neighborFinset z u).mpr huw.symm
      have hv_not : v ∉ G.neighborFinset z := fun h => hnot_vw ((G.mem_neighborFinset z v).mp h).symm
      have hv_not' : v ∉ (G.neighborFinset z).erase u := fun h => hv_not (mem_of_mem_erase h)
      rw [SimpleGraph.degree, edgeShift_neighborFinset_w G huw hvw,
        card_insert_of_notMem hv_not', card_erase_add_one hu_mem, SimpleGraph.degree]
    · rw [SimpleGraph.degree, edgeShift_neighborFinset_other G hvw hzu hzv hzw, SimpleGraph.degree]

/-- **Downward Graphic Closure Under `ExchangeStep` (Lemma 0(1)):**
If `ExchangeStep s₁ s₂` and `s₂` is graphic, then `s₁` is graphic (realized by a single
`edgeShift`). -/
theorem isGraphic_of_exchangeStep {s₁ s₂ : List ℕ}
    (hstep : ExchangeStep s₁ s₂) (hg₂ : IsGraphic s₂) : IsGraphic s₁ := by
  rcases hstep with ⟨hsort₁, _, m, a, b, hba, hb1, hm₁, hm₂⟩
  rcases hg₂ with ⟨n, G, instG, hdegG⟩
  have hmulG : degMultiset G = (a + 1) ::ₘ (b - 1) ::ₘ m := by
    rw [← degList_coe, hdegG, hm₂]
  have ha1_mem : a + 1 ∈ (Finset.univ : Finset (Fin n)).val.map (fun x => G.degree x) := by
    change a + 1 ∈ degMultiset G
    rw [hmulG]
    exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_map.mp ha1_mem with ⟨u, _, hu_deg⟩
  have huniv_u : (Finset.univ : Finset (Fin n)).val = u ::ₘ (Finset.univ.erase u).val := by
    calc
      (Finset.univ : Finset (Fin n)).val = (insert u (Finset.univ.erase u)).val :=
        congrArg Finset.val (insert_erase (mem_univ u)).symm
      _ = u ::ₘ (Finset.univ.erase u).val := Finset.insert_val_of_notMem (notMem_erase u _)
  have hrem_u : (Finset.univ.erase u).val.map (fun x => G.degree x) = (b - 1) ::ₘ m := by
    have h1 : (a + 1) ::ₘ (Finset.univ.erase u).val.map (fun x => G.degree x) =
        (a + 1) ::ₘ (b - 1) ::ₘ m := by
      calc
        (a + 1) ::ₘ (Finset.univ.erase u).val.map (fun x => G.degree x)
            = G.degree u ::ₘ (Finset.univ.erase u).val.map (fun x => G.degree x) := by rw [hu_deg]
        _ = (Finset.univ : Finset (Fin n)).val.map (fun x => G.degree x) := by
            rw [huniv_u, Multiset.map_cons]
        _ = (a + 1) ::ₘ (b - 1) ::ₘ m := hmulG
    exact (Multiset.cons_inj_right (a + 1)).mp h1
  have hb1_mem : b - 1 ∈ (Finset.univ.erase u).val.map (fun x => G.degree x) := by
    rw [hrem_u]
    exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_map.mp hb1_mem with ⟨v, hv_mem_val, hv_deg⟩
  have hv_mem : v ∈ (Finset.univ : Finset (Fin n)).erase u := Finset.mem_def.mpr hv_mem_val
  have huv : u ≠ v := (mem_erase.mp hv_mem).1.symm
  have herase_uv : (Finset.univ.erase u).val = v ::ₘ ((Finset.univ.erase u).erase v).val := by
    calc
      (Finset.univ.erase u).val = (insert v ((Finset.univ.erase u).erase v)).val :=
        congrArg Finset.val (insert_erase hv_mem).symm
      _ = v ::ₘ ((Finset.univ.erase u).erase v).val := Finset.insert_val_of_notMem (notMem_erase v _)
  have hrem_uv : ((Finset.univ.erase u).erase v).val.map (fun x => G.degree x) = m := by
    have h1 : (b - 1) ::ₘ ((Finset.univ.erase u).erase v).val.map (fun x => G.degree x) =
        (b - 1) ::ₘ m := by
      calc
        (b - 1) ::ₘ ((Finset.univ.erase u).erase v).val.map (fun x => G.degree x)
            = G.degree v ::ₘ ((Finset.univ.erase u).erase v).val.map (fun x => G.degree x) := by
                rw [hv_deg]
        _ = (Finset.univ.erase u).val.map (fun x => G.degree x) := by
            rw [herase_uv, Multiset.map_cons]
        _ = (b - 1) ::ₘ m := hrem_u
    exact (Multiset.cons_inj_right (b - 1)).mp h1
  -- Find a neighbor `w` of `u` distinct from `v` and not adjacent to `v`.
  let A : Finset (Fin n) := (G.neighborFinset u).erase v
  let B : Finset (Fin n) := (G.neighborFinset v).erase u
  have hA_card : a ≤ A.card := by
    have h1 : G.degree u - 1 ≤ A.card := by
      rw [SimpleGraph.degree]
      exact Finset.pred_card_le_card_erase
    omega
  have hB_card : B.card ≤ b - 1 := by
    have h1 : B.card ≤ G.degree v := by
      rw [SimpleGraph.degree]
      exact Finset.card_le_card (Finset.erase_subset u _)
    omega
  have hsdiff_pos : 0 < (A \ B).card := by
    have h := Finset.le_card_sdiff B A
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hsdiff_pos
  have hwA : w ∈ A := (mem_sdiff.mp hw).1
  have hw_not_B : w ∉ B := (mem_sdiff.mp hw).2
  have hwv : w ≠ v := (mem_erase.mp hwA).1
  have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (mem_erase.mp hwA).2
  have hwu : w ≠ u := huw.ne.symm
  have hnot_vw : ¬ G.Adj v w := by
    intro h
    exact hw_not_B (mem_erase.mpr ⟨hwu, (G.mem_neighborFinset v w).mpr h⟩)
  let G' : SimpleGraph (Fin n) := edgeShift G u v w
  obtain ⟨hdeg_u', hdeg_v', hdeg_other'⟩ := edgeShift_degree G huw hnot_vw huv hwv.symm
  have hmulG' : degMultiset G' = (s₁ : Multiset ℕ) := by
    unfold degMultiset
    rw [huniv_u, herase_uv, Multiset.map_cons, Multiset.map_cons, hdeg_u', hdeg_v',
      hu_deg, hv_deg, hm₁]
    have ha_eq : a + 1 - 1 = a := by omega
    have hb_eq : b - 1 + 1 = b := by omega
    rw [ha_eq, hb_eq]
    congr 2
    rw [← hrem_uv]
    apply Multiset.map_congr rfl
    intro z hz
    have hz' := Finset.mem_def.mpr hz
    have hzv : z ≠ v := (mem_erase.mp hz').1
    have hzu : z ≠ u := (mem_erase.mp (mem_erase.mp hz').2).1
    exact hdeg_other' z hzu hzv
  refine ⟨n, G', inferInstance, ?_⟩
  exact eq_of_pairwise_ge_of_coe_eq (degList_pairwise G') hsort₁ (by rw [degList_coe, hmulG'])

/-- Downward graphic closure along any finite chain of `ExchangeStep`s. -/
theorem isGraphic_of_exchangeStep_chain {s₁ s₂ : List ℕ}
    (hchain : Relation.ReflTransGen ExchangeStep s₁ s₂) (hg₂ : IsGraphic s₂) :
    IsGraphic s₁ := by
  induction hchain with
  | refl => exact hg₂
  | tail _ hstep ih => exact ih (isGraphic_of_exchangeStep hstep hg₂)

/-- **Classical Havel–Hakimi (Forward / Graphic Descent Direction):**
If `s` is graphic, then `SimpleGraph.havelHakimiStep s` is graphic. -/
theorem isGraphic_havelHakimiStep {s : List ℕ} (hs : IsGraphic s) :
    IsGraphic (SimpleGraph.havelHakimiStep s) := by
  cases s with
  | nil =>
    simp only [SimpleGraph.havelHakimiStep]
    exact ⟨0, ⊥, inferInstance, by simp [degList, degMultiset]⟩
  | cons d rest =>
    rcases hs with ⟨n, G, _, hdegG⟩
    have hd_mem : d ∈ degMultiset G := by
      rw [← degList_coe, hdegG]
      simp
    rcases Multiset.mem_map.mp hd_mem with ⟨v, _, hv_deg⟩
    have hmax : ∀ u : Fin n, G.degree u ≤ G.degree v := by
      intro u
      have hu_mem : G.degree u ∈ d :: rest := by
        rw [← hdegG]
        unfold degList
        rw [Multiset.mem_sort]
        exact Multiset.mem_map.mpr ⟨u, Finset.mem_def.mp (mem_univ u), rfl⟩
      rcases List.mem_cons.mp hu_mem with h | h
      · omega
      · have hpw := degList_pairwise G
        rw [hdegG, List.pairwise_cons] at hpw
        have := hpw.1 _ h
        omega
    have hcons := degList_eq_cons_of_max G v hmax
    rw [hdegG, hv_deg] at hcons
    have hrest : restList G v = rest := (List.cons.inj hcons).2.symm
    have hchain := exchangeStep_chain_of_maxDegDeletion G v
    rw [hv_deg, hrest] at hchain
    exact isGraphic_of_exchangeStep_chain hchain (isGraphic_of_degList (G.induce { u : Fin n | u ≠ v }))

/-- Every graphic sequence satisfies `IsHHValid`. -/
theorem isHHValid_of_isGraphic : ∀ {s : List ℕ}, IsGraphic s → IsHHValid s := by
  intro s
  induction hlen : s.length using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    intro hs
    cases s with
    | nil => simp
    | cons d rest =>
      rw [isHHValid_cons]
      have hhh_graphic : IsGraphic (SimpleGraph.havelHakimiStep (d :: rest)) :=
        isGraphic_havelHakimiStep hs
      rcases hs with ⟨n, G, _, hdegG⟩
      have hd_mem : d ∈ degMultiset G := by
        rw [← degList_coe, hdegG]
        simp
      rcases Multiset.mem_map.mp hd_mem with ⟨v, _, hv_deg⟩
      have hmax : ∀ u : Fin n, G.degree u ≤ G.degree v := by
        intro u
        have hu_mem : G.degree u ∈ d :: rest := by
          rw [← hdegG]
          unfold degList
          rw [Multiset.mem_sort]
          exact Multiset.mem_map.mpr ⟨u, Finset.mem_def.mp (mem_univ u), rfl⟩
        rcases List.mem_cons.mp hu_mem with h | h
        · omega
        · have hpw := degList_pairwise G
          rw [hdegG, List.pairwise_cons] at hpw
          have := hpw.1 _ h
          omega
      have hcons := degList_eq_cons_of_max G v hmax
      rw [hdegG, hv_deg] at hcons
      have hrest : rest = restList G v := (List.cons.inj hcons).2
      subst hrest
      obtain ⟨S, hScard, hSpos, _⟩ := induce_ne_degList_as_indexed_decrement G v
      rw [hv_deg] at hScard
      have hd_le : d ≤ (restList G v).length := by
        rw [← hScard]
        exact (Finset.card_le_univ S).trans (by simp)
      have htake_pos : ∀ x ∈ (restList G v).take d, 1 ≤ x := by
        intro x hx
        have hmem_top : x ∈ (topFinset (restList G v).length d).val.map (fun i => (restList G v)[i]) := by
          rw [← list_take_coe_eq_topFinset_map]
          exact Multiset.mem_coe.mpr hx
        rcases Multiset.mem_map.mp hmem_top with ⟨i, hi_top, rfl⟩
        by_cases hiS : i ∈ S
        · exact hSpos i hiS
        · -- Since `|S| = d = |topFinset|` and `i ∈ topFinset \ S`, there exists `j ∈ S \ topFinset`.
          have hi_top' : i ∈ topFinset (restList G v).length d := Finset.mem_def.mpr hi_top
          have hcard_top : (topFinset (restList G v).length d).card = d := card_topFinset hd_le
          have h1 := Finset.card_sdiff_add_card_inter (topFinset (restList G v).length d) S
          have h2 := Finset.card_sdiff_add_card_inter S (topFinset (restList G v).length d)
          rw [Finset.inter_comm] at h2
          have hpos_diff : 0 < (topFinset (restList G v).length d \ S).card :=
            Finset.card_pos.mpr ⟨i, mem_sdiff.mpr ⟨hi_top', hiS⟩⟩
          have hSdiff_pos : 0 < (S \ topFinset (restList G v).length d).card := by omega
          obtain ⟨j, hj⟩ := Finset.card_pos.mp hSdiff_pos
          have hjS : j ∈ S := (mem_sdiff.mp hj).1
          have hj_not : j ∉ topFinset (restList G v).length d := (mem_sdiff.mp hj).2
          have hi_lt : i.1 < d := (mem_filter.mp hi_top').2
          have hj_ge : d ≤ j.1 := by
            simp only [topFinset, mem_filter, mem_univ, true_and, not_lt] at hj_not
            exact hj_not
          have hrest_pw : (restList G v).Pairwise (· ≥ ·) := restList_pairwise G v
          have hle : (restList G v)[j] ≤ (restList G v)[i] :=
            pairwise_ge_getElem_le hrest_pw i.2 j.2 (by omega)
          exact (hSpos j hjS).trans hle
      refine ⟨hd_le, htake_pos, ?_⟩
      apply ih (SimpleGraph.havelHakimiStep (d :: restList G v)).length
      · rw [SimpleGraph.havelHakimiStep_length_cons, ← hlen]
        simp
      · rfl
      · exact hhh_graphic

/-- Graph extension adding a new apex vertex `none : Option V` adjacent to exactly `A : Finset V`. -/
def addApex {V : Type*} (H : SimpleGraph V) (A : Finset V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some j => j ∈ A
    | some i, none => i ∈ A
    | some i, some j => H.Adj i j
  symm := ⟨by
    rintro (_ | i) (_ | j) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | i) h
    · exact h
    · exact H.loopless.irrefl i h⟩

instance instDecidableRelAddApex {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) :
    DecidableRel (addApex H A).Adj
  | none, none => isFalse id
  | none, some j => inferInstanceAs (Decidable (j ∈ A))
  | some i, none => inferInstanceAs (Decidable (i ∈ A))
  | some i, some j => inferInstanceAs (Decidable (H.Adj i j))

private lemma addApex_degree_none {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) :
    (addApex H A).degree none = A.card := by
  let someEmb : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have hnb : (addApex H A).neighborFinset none = A.map someEmb := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x with
    | none => simp [addApex, someEmb]
    | some j => simp [addApex, someEmb]
  rw [SimpleGraph.degree, hnb, card_map]

private lemma addApex_degree_some {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) (i : V) :
    (addApex H A).degree (some i) = if i ∈ A then H.degree i + 1 else H.degree i := by
  let someEmb : V ↪ Option V := ⟨some, Option.some_injective V⟩
  by_cases hi : i ∈ A
  · have hnb : (addApex H A).neighborFinset (some i) =
        insert none ((H.neighborFinset i).map someEmb) := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x with
      | none => simp [addApex, hi]
      | some j => simp [addApex, someEmb, SimpleGraph.mem_neighborFinset]
    have hnone_not : none ∉ (H.neighborFinset i).map someEmb := by
      simp [someEmb]
    rw [ite_eq_left hi, SimpleGraph.degree, hnb, card_insert_of_notMem hnone_not, card_map,
      SimpleGraph.degree]
  · have hnb : (addApex H A).neighborFinset (some i) = (H.neighborFinset i).map someEmb := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x with
      | none => simp [addApex, hi, someEmb]
      | some j => simp [addApex, someEmb, SimpleGraph.mem_neighborFinset]
    rw [ite_eq_right hi, SimpleGraph.degree, hnb, card_map, SimpleGraph.degree]

private lemma list_map_sub_one_add_one {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) :
    l.map ((· + 1) ∘ (· - 1)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : 1 ≤ x := h x (by simp)
    have hxs : ∀ y ∈ xs, 1 ≤ y := fun y hy => h y (by simp [hy])
    simp only [List.map_cons, Function.comp_apply, ih hxs]
    congr 1
    omega

/-- **Classical Havel–Hakimi (Converse / Synthesis Direction):**
Every descending sorted sequence satisfying `IsHHValid` is graphic. -/
theorem isGraphic_of_isHHValid : ∀ {s : List ℕ}, s.Pairwise (· ≥ ·) → IsHHValid s → IsGraphic s := by
  intro s
  induction hlen : s.length using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    intro hsort hvalid
    cases s with
    | nil =>
      exact ⟨0, ⊥, inferInstance, by simp [degList, degMultiset]⟩
    | cons d rest =>
      rw [isHHValid_cons] at hvalid
      rcases hvalid with ⟨hd_le, htake_pos, hhh_valid⟩
      have hhh_graphic : IsGraphic (SimpleGraph.havelHakimiStep (d :: rest)) := by
        apply ih (SimpleGraph.havelHakimiStep (d :: rest)).length
        · rw [SimpleGraph.havelHakimiStep_length_cons, ← hlen]
          simp
        · rfl
        · exact havelHakimiStep_pairwise _
        · exact hhh_valid
      rcases hhh_graphic with ⟨k, H, _, hdegH⟩
      have hk_len : k = rest.length := by
        have h1 := degList_length H
        rw [hdegH, SimpleGraph.havelHakimiStep_length_cons, Fintype.card_fin] at h1
        exact h1.symm
      -- Partition `Fin k` into `A` (realizing `(rest.take d).map (· - 1)`) and `univ \ A` (`rest.drop d`).
      let degOfFn : List ℕ := List.ofFn (fun i : Fin k => H.degree i)
      have hdegOfFn_coe : (degOfFn : Multiset ℕ) =
          (((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ) + (rest.drop d : Multiset ℕ) := by
        have h1 : (degOfFn : Multiset ℕ) = degMultiset H := by
          unfold degMultiset degOfFn
          rw [← finRange_coe_eq_univ_val, Multiset.map_coe, List.ofFn_eq_map]
        rw [h1, ← degList_coe, hdegH, havelHakimiStep_coe]
      obtain ⟨S, hSA, hSB⟩ := exists_finset_of_multiset_add degOfFn
        (((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ) (rest.drop d : Multiset ℕ) hdegOfFn_coe
      have hlen_ofFn : degOfFn.length = k := List.length_ofFn
      let eLen : Fin degOfFn.length ≃ Fin k := Fin.castOrderIso hlen_ofFn |>.toEquiv
      let A : Finset (Fin k) := S.map eLen.toEmbedding
      have hA_map : A.val.map (fun i => H.degree i) =
          (((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
        rw [Finset.map_val, Multiset.map_map, ← hSA]
        apply Multiset.map_congr rfl
        intro i _
        change H.degree (eLen i) = (List.ofFn (fun j : Fin k => H.degree j))[i.1]'(by simpa [degOfFn] using i.2)
        rw [List.getElem_ofFn]
        rfl
      have hcompl_A : Finset.univ \ A = (Finset.univ \ S).map eLen.toEmbedding := by
        ext j
        simp only [A, mem_sdiff, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
        constructor
        · intro hj
          refine ⟨eLen.symm j, ?_, eLen.apply_symm_apply j⟩
          intro hmem
          exact hj ⟨eLen.symm j, hmem, eLen.apply_symm_apply j⟩
        · rintro ⟨i, hi, rfl⟩ ⟨i', hi', heq⟩
          exact hi (eLen.injective heq ▸ hi')
      have hB_map : (Finset.univ \ A).val.map (fun i => H.degree i) = (rest.drop d : Multiset ℕ) := by
        rw [hcompl_A, Finset.map_val, Multiset.map_map, ← hSB]
        apply Multiset.map_congr rfl
        intro i _
        change H.degree (eLen i) = (List.ofFn (fun j : Fin k => H.degree j))[i.1]'(by simpa [degOfFn] using i.2)
        rw [List.getElem_ofFn]
        rfl
      have hA_card : A.card = d := by
        have h1 : A.card = (((rest.take d).map (· - 1) : List ℕ) : Multiset ℕ).card := by
          rw [← hA_map, Multiset.card_map]
          rfl
        simp only [Multiset.coe_card, List.length_map, List.length_take] at h1
        omega
      -- Extend `H` by adding an apex adjacent to `A`.
      let G : SimpleGraph (Option (Fin k)) := addApex H A
      let someEmb : Fin k ↪ Option (Fin k) := ⟨some, Option.some_injective _⟩
      have huniv_opt : (Finset.univ : Finset (Option (Fin k))) =
          insert none ((Finset.univ : Finset (Fin k)).map someEmb) := by
        ext x
        cases x with
        | none => simp
        | some i => simp [someEmb]
      have hnone_not : none ∉ (Finset.univ : Finset (Fin k)).map someEmb := by
        simp [someEmb]
      have huniv_split : (Finset.univ : Finset (Fin k)).val = A.val + (Finset.univ \ A).val := by
        have hdisj : Disjoint A (Finset.univ \ A) := disjoint_sdiff_self_right
        have hunion : A ∪ (Finset.univ \ A) = Finset.univ :=
          Finset.union_sdiff_of_subset (Finset.subset_univ _)
        calc
          (Finset.univ : Finset (Fin k)).val = (A ∪ (Finset.univ \ A)).val :=
            congrArg Finset.val hunion.symm
          _ = A.val + (Finset.univ \ A).val := finset_union_val_of_disjoint hdisj
      have hmulG : degMultiset G = ((d :: rest : List ℕ) : Multiset ℕ) := by
        unfold degMultiset
        rw [huniv_opt, Finset.insert_val_of_notMem hnone_not, Multiset.map_cons,
          addApex_degree_none H A, hA_card, Finset.map_val, Multiset.map_map]
        have hsome_fun : ((fun x => G.degree x) ∘ ⇑someEmb) =
            (fun i => if i ∈ A then H.degree i + 1 else H.degree i) := by
          funext i
          exact addApex_degree_some H A i
        rw [hsome_fun, huniv_split, Multiset.map_add]
        have hpartA : A.val.map (fun i => if i ∈ A then H.degree i + 1 else H.degree i) =
            (rest.take d : Multiset ℕ) := by
          have h1 : A.val.map (fun i => if i ∈ A then H.degree i + 1 else H.degree i) =
              (A.val.map (fun i => H.degree i)).map (· + 1) := by
            rw [Multiset.map_map]
            apply Multiset.map_congr rfl
            intro i hi
            simp [Finset.mem_def.mpr hi]
          rw [h1, hA_map, Multiset.map_coe, List.map_map]
          congr 1
          exact list_map_sub_one_add_one htake_pos
        have hpartB : (Finset.univ \ A).val.map
            (fun i => if i ∈ A then H.degree i + 1 else H.degree i) =
            (rest.drop d : Multiset ℕ) := by
          rw [← hB_map]
          apply Multiset.map_congr rfl
          intro i hi
          have hnot : i ∉ A := (mem_sdiff.mp (Finset.mem_def.mpr hi)).2
          simp [hnot]
        rw [hpartA, hpartB, Multiset.coe_add, List.take_append_drop]
        rfl
      have hdegG : degList G = d :: rest :=
        eq_of_pairwise_ge_of_coe_eq (degList_pairwise G) hsort (by rw [degList_coe, hmulG])
      rw [← hdegG]
      exact isGraphic_of_degList G

/-- **Classical Havel–Hakimi Equivalence:**
A list `s : List ℕ` is graphic if and only if it is sorted descending and `IsHHValid s`. -/
theorem isGraphic_iff_sorted_hhValid (s : List ℕ) :
    IsGraphic s ↔ s.Pairwise (· ≥ ·) ∧ IsHHValid s :=
  ⟨fun h => ⟨isGraphic_pairwise h, isHHValid_of_isGraphic h⟩,
   fun ⟨hs, hv⟩ => isGraphic_of_isHHValid hs hv⟩

/-- Downward closure of `IsHHValid` under `ExchangeStep`. -/
theorem isHHValid_of_exchangeStep {s₁ s₂ : List ℕ}
    (hstep : ExchangeStep s₁ s₂) (hv₂ : IsHHValid s₂) : IsHHValid s₁ :=
  isHHValid_of_isGraphic (isGraphic_of_exchangeStep hstep (isGraphic_of_isHHValid hstep.2.1 hv₂))

/-- Lift an `ExchangeStep` chain ending at a graphic list to a chain where every intermediate
node is `IsGraphic`. -/
theorem graphic_exchangeStep_chain_of_end {s₁ s₂ : List ℕ}
    (hchain : Relation.ReflTransGen ExchangeStep s₁ s₂) (hg₂ : IsGraphic s₂) :
    Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsGraphic a ∧ IsGraphic b) s₁ s₂ := by
  induction hchain with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have hgb : IsGraphic b := isGraphic_of_exchangeStep hbc hg₂
    exact Relation.ReflTransGen.tail (ih hgb) ⟨hbc, hgb, hg₂⟩

/-- Lift an `ExchangeStep` chain ending at an HH-valid list to a chain where every intermediate
node is `IsHHValid`. -/
theorem hhValid_exchangeStep_chain_of_end {s₁ s₂ : List ℕ}
    (hchain : Relation.ReflTransGen ExchangeStep s₁ s₂) (hv₂ : IsHHValid s₂) :
    Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsHHValid a ∧ IsHHValid b) s₁ s₂ := by
  induction hchain with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have hvb : IsHHValid b := isHHValid_of_exchangeStep hbc hv₂
    exact Relation.ReflTransGen.tail (ih hvb) ⟨hbc, hvb, hv₂⟩

/-- **Graphic Exchange Chain for Max-Degree Vertex Deletion:**
Every intermediate sequence along the `ExchangeStep` chain from
`havelHakimiStep (Q.degree v :: restList Q v)` to `degList (Q - v)` is graphic. -/
theorem graphic_exchangeStep_chain_of_maxDegDeletion {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsGraphic a ∧ IsGraphic b)
      (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v))
      (degList (Q.induce { u : V | u ≠ v })) :=
  graphic_exchangeStep_chain_of_end
    (exchangeStep_chain_of_maxDegDeletion Q v)
    (isGraphic_of_degList (Q.induce { u : V | u ≠ v }))

/-- **HH-Valid Exchange Chain for Max-Degree Vertex Deletion:**
Every intermediate sequence along the `ExchangeStep` chain from
`havelHakimiStep (Q.degree v :: restList Q v)` to `degList (Q - v)` satisfies `IsHHValid`. -/
theorem hhValid_exchangeStep_chain_of_maxDegDeletion {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V) :
    Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsHHValid a ∧ IsHHValid b)
      (SimpleGraph.havelHakimiStep (Q.degree v :: restList Q v))
      (degList (Q.induce { u : V | u ≠ v })) :=
  hhValid_exchangeStep_chain_of_end
    (exchangeStep_chain_of_maxDegDeletion Q v)
    (isHHValid_of_isGraphic (isGraphic_of_degList (Q.induce { u : V | u ≠ v })))

end HavelHakimiClosure

end WOWII61.ResidueGraph
