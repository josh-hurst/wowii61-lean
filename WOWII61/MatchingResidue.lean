module

public import WOWII61.PackingForest
public import WOWII61.SimultaneousPairBound

/-!
# Matching Residue Theorem, IMR, and Full WOWII Conjecture 61

This module formalizes the general matching-residue induction and IMR theorem, reusing the
precompiled sibling modules `PackingForest` and `SimultaneousPairBound` without modifying any
sibling source file:

1. **Batch Independent Max-Degree Deletion (`residue_le_induce_compl_of_indep_maxDeg`):**
   from `WOWII61.PackingBound.MaxDegDeletionResiduePremise`, deleting an independent set `X`
   of vertices all sharing the same positive maximum degree `d` cannot decrease
   `SimpleGraph.residue`.
2. **Matching Theorem (`matching_theorem_of_maxDegDeletion`):**
   for any finite simple graph `K` and disjoint vertex sets `A, B` whose union `A ∪ B` is
   independent in `K`, letting `T = completeBipartiteJoin K A B` be `K` with all edges between
   `A` and `B` added, there exists a matching `M` between `A` and `B` saturating the smaller
   side (`IsMaxABMatching A B M`) such that `SimpleGraph.residue (K ⊔ M) ≤ T.indepNum`.
3. **Induced-Matching Residue Inequality (`imr_of_maxDegDeletion`,
   `imr_premise_of_maxDegDeletion`):**
   for any finite simple graph `G` and any induced matching `M : InducedMatching G k`,
   `SimpleGraph.residue G ≤ max (G.induce { u | u ∉ M.A }).indepNum (G.induce { u | u ∉ M.B }).indepNum`.
4. **Full WOWII Conjecture 61 (`wowii61_of_maxDegDeletion`,
   `wowii61_of_maxDegDeletion_nontrivial`):**
   for every finite connected simple graph `G`, assuming only `MaxDegDeletionResiduePremise`,
   `SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`.
-/

@[expose] public section

namespace WOWII61.MatchingResidue

open SimpleGraph Finset WOWII61.PackingForest WOWII61.PackingBound

/-! ## 1. Graph Helpers, Degree Equality, and Independent Max-Degree Batch Deletion -/

section GraphHelpers

/-- Pointwise equality of vertex degrees implies equality of `SimpleGraph.residue`. -/
theorem residue_eq_of_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hdeg : ∀ v : V, G.degree v = H.degree v) :
    SimpleGraph.residue G = SimpleGraph.residue H := by
  unfold SimpleGraph.residue
  have hfun : (fun v : V => G.degree v) = (fun v : V => H.degree v) := funext hdeg
  rw [hfun]

/-- Vertex degree in an induced subgraph is at most the degree in the ambient graph. -/
theorem induce_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (u : S) :
    (G.induce S).degree u ≤ G.degree u.1 := by
  have hsub : ((G.induce S).neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
      G.neighborFinset u.1 := by
    intro w hw
    rcases mem_map.mp hw with ⟨w', hw', rfl⟩
    exact (G.mem_neighborFinset u.1 w'.1).mpr (((G.induce S).mem_neighborFinset u w').mp hw')
  have hle := card_le_card hsub
  rwa [card_map] at hle

/-- If every neighbor of `u` lies in `S`, then `u` keeps the exact same degree in `G.induce S`. -/
theorem induce_degree_eq_of_no_adj_outside {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (u : S)
    (hno : ∀ w : V, G.Adj u.1 w → w ∈ S) :
    (G.induce S).degree u = G.degree u.1 := by
  have heq : ((G.induce S).neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩ =
      G.neighborFinset u.1 := by
    ext w
    simp only [mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨w', hw', rfl⟩
      exact hw'
    · intro hw
      exact ⟨⟨w, hno w hw⟩, hw, rfl⟩
  calc
    (G.induce S).degree u
        = (((G.induce S).neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩).card :=
          (card_map _).symm
    _ = (G.neighborFinset u.1).card := by rw [heq]
    _ = G.degree u.1 := rfl

/-- Taking an induced subgraph cannot increase the independence number. -/
theorem induce_indepNum_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) :
    (G.induce S).indepNum ≤ G.indepNum := by
  obtain ⟨I, hI⟩ := (G.induce S).exists_isNIndepSet_indepNum
  let J : Finset V := I.map ⟨Subtype.val, Subtype.val_injective⟩
  have hJ : G.IsIndepSet (J : Set V) := by
    intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases hb with ⟨b0, hb0, rfl⟩
    exact hI.isIndepSet (mem_coe.mpr ha0) (mem_coe.mpr hb0) (fun h => hab (congrArg Subtype.val h))
  have hcard : J.card = (G.induce S).indepNum := by
    rw [card_map, hI.card_eq]
  rw [← hcard]
  exact hJ.card_le_indepNum

private lemma card_univ_filter_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Prop) [DecidablePred P] (X : Finset V) :
    (Finset.univ.filter (fun u : { u : V // P u } => u.1 ∈ X)).card =
      (X.filter P).card := by
  have hmap : (Finset.univ.filter (fun u : { u : V // P u } => u.1 ∈ X)).map
      ⟨Subtype.val, Subtype.val_injective⟩ = X.filter P := by
    ext u
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨v, hv⟩, hvX, rfl⟩
      exact ⟨hvX, hv⟩
    · rintro ⟨huX, huP⟩
      exact ⟨⟨u, huP⟩, huX, rfl⟩
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap]

private lemma card_subtype_not_mem {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    Fintype.card { u : V // u ∉ S } + S.card = Fintype.card V := by
  have h1 := Fintype.card_subtype_compl (fun u : V => u ∈ S)
  have h2 : Fintype.card { u : V // u ∈ S } = S.card := Fintype.card_coe S
  have hle : S.card ≤ Fintype.card V := by
    simpa [Finset.card_univ] using Finset.card_le_univ S
  change Fintype.card { u : V // ¬ u ∈ S } + S.card = Fintype.card V
  omega

private theorem residue_le_induce_compl_of_indep_maxDeg_aux
    (hDel : MaxDegDeletionResiduePremise) :
    ∀ (k : ℕ) {V : Type u} [Fintype V] [DecidableEq V]
      (Q : SimpleGraph V) [DecidableRel Q.Adj]
      (X : Finset V) (d : ℕ),
      X.card = k → 0 < d →
      Q.IsIndepSet (X : Set V) →
      (∀ x ∈ X, Q.degree x = d) →
      (∀ u : V, Q.degree u ≤ d) →
      SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : V | u ∉ X }) := by
  intro k
  induction k with
  | zero =>
    intro V _ _ Q _ X d hXcard _ _ _ _
    have hXempty : X = ∅ := Finset.card_eq_zero.mp hXcard
    let iso : Q ≃g Q.induce { u : V | u ∉ X } :=
      { toFun := fun u => ⟨u, by simp [hXempty]⟩
        invFun := fun u => u.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    rw [residue_eq_of_iso iso]
  | succ k ih =>
    intro V _ _ Q _ X d hXcard hd hX_indep hX_deg hmax
    obtain ⟨x, hxX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    have hx_deg : Q.degree x = d := hX_deg x hxX
    have hx_max : ∀ u : V, Q.degree u ≤ Q.degree x := fun u => hx_deg ▸ hmax u
    have hx_pos : 0 < Q.degree x := hx_deg ▸ hd
    have hstep : SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : V | u ≠ x }) :=
      hDel.apply Q x hx_max hx_pos
    let V' := { u : V // u ≠ x }
    let Q' : SimpleGraph V' := Q.induce { u : V | u ≠ x }
    let X' : Finset V' := Finset.univ.filter (fun u : V' => u.1 ∈ X)
    have hX'_card : X'.card = k := by
      have h1 := card_univ_filter_subtype (fun u : V => u ≠ x) X
      have h2 : X.filter (fun u : V => u ≠ x) = X.erase x := by
        ext u
        simp [and_comm]
      have h3 : (X.erase x).card = k := by
        have := Finset.card_erase_add_one hxX
        omega
      dsimp only [X']
      rw [h1, h2, h3]
    have hX'_indep : Q'.IsIndepSet (X' : Set V') := by
      intro a ha b hb hab
      have haX : a.1 ∈ X := (mem_filter.mp (mem_coe.mp ha)).2
      have hbX : b.1 ∈ X := (mem_filter.mp (mem_coe.mp hb)).2
      exact hX_indep (mem_coe.mpr haX) (mem_coe.mpr hbX) (fun h => hab (Subtype.ext h))
    have hX'_deg : ∀ u ∈ X', Q'.degree u = d := by
      intro u hu
      have huX : u.1 ∈ X := (mem_filter.mp hu).2
      have hno : ∀ w : V, Q.Adj u.1 w → w ≠ x := by
        intro w huw hwx
        subst hwx
        exact hX_indep (mem_coe.mpr huX) (mem_coe.mpr hxX) u.2 huw
      calc
        Q'.degree u = Q.degree u.1 :=
          induce_degree_eq_of_no_adj_outside Q { w : V | w ≠ x } u hno
        _ = d := hX_deg u.1 huX
    have hmax' : ∀ u : V', Q'.degree u ≤ d := fun u =>
      (induce_degree_le Q { w : V | w ≠ x } u).trans (hmax u.1)
    have hrec : SimpleGraph.residue Q' ≤ SimpleGraph.residue (Q'.induce { u : V' | u ∉ X' }) :=
      ih Q' X' d hX'_card hd hX'_indep hX'_deg hmax'
    let iso : Q'.induce { u : V' | u ∉ X' } ≃g Q.induce { u : V | u ∉ X } :=
      { toFun := fun u => ⟨u.1.1, fun h => u.2 (mem_filter.mpr ⟨mem_univ _, h⟩)⟩
        invFun := fun u =>
          ⟨⟨u.1, fun h => u.2 (h ▸ hxX)⟩, fun h => u.2 (mem_filter.mp h).2⟩
        left_inv := fun u => Subtype.ext (Subtype.ext rfl)
        right_inv := fun u => Subtype.ext rfl
        map_rel_iff' := Iff.rfl }
    calc
      SimpleGraph.residue Q ≤ SimpleGraph.residue Q' := hstep
      _ ≤ SimpleGraph.residue (Q'.induce { u : V' | u ∉ X' }) := hrec
      _ = SimpleGraph.residue (Q.induce { u : V | u ∉ X }) := residue_eq_of_iso iso

/-- **Batch Independent Max-Degree Deletion:**
deleting an independent set `X` whose vertices all share the same positive maximum degree `d`
cannot decrease `SimpleGraph.residue`. -/
theorem residue_le_induce_compl_of_indep_maxDeg
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (X : Finset V) (d : ℕ) (hd : 0 < d)
    (hX_indep : Q.IsIndepSet (X : Set V))
    (hX_deg : ∀ x ∈ X, Q.degree x = d)
    (hmax : ∀ u : V, Q.degree u ≤ d)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : V | u ∉ X }) :=
  residue_le_induce_compl_of_indep_maxDeg_aux hDel X.card Q X d rfl hd hX_indep hX_deg hmax

end GraphHelpers

/-! ## 2. Bipartite Join, Edge Removal, and Maximum Bipartite Matchings -/

section BipartiteMatching

variable {V : Type*}

/-- `completeBipartiteJoin K A B` adds all edges between `A` and `B` (between distinct vertices)
to `K` (complete bipartite join `T` between `A` and `B`). -/
def completeBipartiteJoin (K : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj u v := K.Adj u v ∨ (u ≠ v ∧ ((u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)))
  symm := ⟨fun _ _ h => by
    rcases h with hK | ⟨hne, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact Or.inl hK.symm
    · exact Or.inr ⟨hne.symm, Or.inr ⟨hv, hu⟩⟩
    · exact Or.inr ⟨hne.symm, Or.inl ⟨hv, hu⟩⟩⟩
  loopless := ⟨fun u h => by
    rcases h with hK | ⟨hne, _⟩
    · exact K.loopless.irrefl u hK
    · exact hne rfl⟩

theorem completeBipartiteJoin_comm (K : SimpleGraph V) (A B : Finset V) :
    completeBipartiteJoin K A B = completeBipartiteJoin K B A := by
  ext u v
  simp only [completeBipartiteJoin]
  tauto

theorem completeBipartiteJoin_empty_left (K : SimpleGraph V) (B : Finset V) :
    completeBipartiteJoin K ∅ B = K := by
  ext u v
  simp [completeBipartiteJoin]

theorem completeBipartiteJoin_adj_of_disjoint (K : SimpleGraph V) {A B : Finset V}
    (hdisj : Disjoint A B) (u v : V) :
    (completeBipartiteJoin K A B).Adj u v ↔ K.Adj u v ∨ (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
  simp only [completeBipartiteJoin]
  constructor
  · rintro (hK | ⟨_, hAB⟩)
    · exact Or.inl hK
    · exact Or.inr hAB
  · rintro (hK | ⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact Or.inl hK
    · exact Or.inr ⟨fun h => Finset.disjoint_left.mp hdisj hu (h ▸ hv), Or.inl ⟨hu, hv⟩⟩
    · exact Or.inr ⟨fun h => Finset.disjoint_left.mp hdisj hv (h ▸ hu), Or.inr ⟨hu, hv⟩⟩

/-- `removeBetween G A B` removes all edges of `G` having one endpoint in `A` and the other
in `B`. -/
def removeBetween (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ ((u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
  symm := ⟨fun _ _ h => by
    refine ⟨h.1.symm, ?_⟩
    rintro (⟨hv, hu⟩ | ⟨hv, hu⟩)
    · exact h.2 (Or.inr ⟨hu, hv⟩)
    · exact h.2 (Or.inl ⟨hu, hv⟩)⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- A simple graph `M` is a matching between `A` and `B` if every edge of `M` has one
endpoint in `A` and the other in `B`, and every vertex has at most one `M`-neighbor. -/
structure IsABMatching (A B : Finset V) (M : SimpleGraph V) : Prop where
  edges_between : ∀ u v : V, M.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)
  unique_neighbor : ∀ u v w : V, M.Adj u v → M.Adj u w → v = w

/-- A matching `M` between `A` and `B` has maximum size `min |A| |B|` iff it saturates at least
one of the two sides `A` or `B`. -/
structure IsMaxABMatching (A B : Finset V) (M : SimpleGraph V) : Prop extends
    IsABMatching A B M where
  saturates : (∀ a ∈ A, ∃ b ∈ B, M.Adj a b) ∨ (∀ b ∈ B, ∃ a ∈ A, M.Adj a b)

theorem IsABMatching.symm {A B : Finset V} {M : SimpleGraph V} (hM : IsABMatching A B M) :
    IsABMatching B A M where
  edges_between u v huv := (hM.edges_between u v huv).symm
  unique_neighbor := hM.unique_neighbor

theorem IsMaxABMatching.symm {A B : Finset V} {M : SimpleGraph V} (hM : IsMaxABMatching A B M) :
    IsMaxABMatching B A M where
  toIsABMatching := hM.toIsABMatching.symm
  saturates := hM.saturates.symm.imp
    (fun hB b hb => let ⟨a, ha, hab⟩ := hB b hb; ⟨a, ha, hab.symm⟩)
    (fun hA a ha => let ⟨b, hb, hab⟩ := hA a ha; ⟨b, hb, hab.symm⟩)

section MatchingDegrees

variable [Fintype V]

theorem IsABMatching.degree_le_one {A B : Finset V} {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsABMatching A B M) (u : V) : M.degree u ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact hM.unique_neighbor u v w
    ((M.mem_neighborFinset u v).mp hv)
    ((M.mem_neighborFinset u w).mp hw)

theorem IsABMatching.degree_eq_one_iff {A B : Finset V} {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsABMatching A B M) (u : V) :
    M.degree u = 1 ↔ ∃ v : V, M.Adj u v := by
  constructor
  · intro h1
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < M.degree u)
    exact ⟨v, (M.mem_neighborFinset u v).mp hv⟩
  · rintro ⟨v, huv⟩
    have hpos : 0 < M.degree u := Finset.card_pos.mpr ⟨v, (M.mem_neighborFinset u v).mpr huv⟩
    have hle : M.degree u ≤ 1 := hM.degree_le_one u
    omega

theorem IsABMatching.degree_eq_zero_iff {A B : Finset V} {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsABMatching A B M) (u : V) :
    M.degree u = 0 ↔ ∀ v : V, ¬ M.Adj u v := by
  have h1 := hM.degree_eq_one_iff u
  have hle := hM.degree_le_one u
  constructor
  · intro h0 v huv
    have : M.degree u = 1 := h1.mpr ⟨v, huv⟩
    omega
  · intro hno
    by_contra hne
    have : M.degree u = 1 := by omega
    obtain ⟨v, huv⟩ := h1.mp this
    exact hno v huv

theorem IsABMatching.degree_eq_zero_of_not_mem {A B : Finset V} {M : SimpleGraph V}
    [DecidableRel M.Adj] (hM : IsABMatching A B M) {u : V} (huA : u ∉ A) (huB : u ∉ B) :
    M.degree u = 0 := by
  rw [hM.degree_eq_zero_iff]
  intro v huv
  rcases hM.edges_between u v huv with ⟨h, _⟩ | ⟨h, _⟩
  · exact huA h
  · exact huB h

/-- Double counting matching edges across the bipartition `(A, B)`:
`∑ a ∈ A, M.degree a = ∑ b ∈ B, M.degree b`. -/
theorem IsABMatching.sum_degree_left_eq_sum_degree_right {A B : Finset V}
    (hdisj : Disjoint A B) {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsABMatching A B M) :
    ∑ a ∈ A, M.degree a = ∑ b ∈ B, M.degree b := by
  have hA : ∀ a ∈ A, M.degree a = ∑ b ∈ B, if M.Adj a b then 1 else 0 := by
    intro a ha
    have hnb : M.neighborFinset a = B.filter (fun b => M.Adj a b) := by
      ext b
      simp only [SimpleGraph.mem_neighborFinset, mem_filter]
      constructor
      · intro hab
        rcases hM.edges_between a b hab with ⟨_, hb⟩ | ⟨haB, _⟩
        · exact ⟨hb, hab⟩
        · exact absurd haB (Finset.disjoint_left.mp hdisj ha)
      · exact fun h => h.2
    simp only [SimpleGraph.degree, hnb, Finset.card_filter]
  have hB : ∀ b ∈ B, M.degree b = ∑ a ∈ A, if M.Adj a b then 1 else 0 := by
    intro b hb
    have hnb : M.neighborFinset b = A.filter (fun a => M.Adj a b) := by
      ext a
      simp only [SimpleGraph.mem_neighborFinset, mem_filter]
      constructor
      · intro hba
        rcases hM.edges_between b a hba with ⟨hbA, _⟩ | ⟨_, haA⟩
        · exact absurd hbA (Finset.disjoint_right.mp hdisj hb)
        · exact ⟨haA, hba.symm⟩
      · exact fun h => h.2.symm
    simp only [SimpleGraph.degree, hnb, Finset.card_filter]
  calc
    ∑ a ∈ A, M.degree a
        = ∑ a ∈ A, ∑ b ∈ B, if M.Adj a b then 1 else 0 := Finset.sum_congr rfl hA
    _ = ∑ b ∈ B, ∑ a ∈ A, if M.Adj a b then 1 else 0 := Finset.sum_comm
    _ = ∑ b ∈ B, M.degree b := (Finset.sum_congr rfl hB).symm

theorem IsABMatching.card_matched_left_eq_right {A B : Finset V}
    (hdisj : Disjoint A B) {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsABMatching A B M) :
    (A.filter (fun a => M.degree a = 1)).card = (B.filter (fun b => M.degree b = 1)).card := by
  have hsum : ∀ S : Finset V, (S.filter (fun u => M.degree u = 1)).card = ∑ u ∈ S, M.degree u := by
    intro S
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro u _
    have hle := hM.degree_le_one u
    split_ifs <;> omega
  rw [hsum A, hsum B]
  exact hM.sum_degree_left_eq_sum_degree_right hdisj

/-- If `|A| ≤ |B|`, every maximum matching between `A` and `B` matches every vertex of `A`. -/
theorem IsMaxABMatching.forall_degree_eq_one_left_of_card_le {A B : Finset V}
    (hdisj : Disjoint A B) {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsMaxABMatching A B M) (hcard : A.card ≤ B.card) :
    ∀ a ∈ A, M.degree a = 1 := by
  rcases hM.saturates with hA | hB
  · intro a ha
    obtain ⟨b, _, hab⟩ := hA a ha
    exact (hM.degree_eq_one_iff a).mpr ⟨b, hab⟩
  · have hB_eq : B.filter (fun b => M.degree b = 1) = B := by
      rw [Finset.filter_eq_self]
      intro b hb
      obtain ⟨a, _, hab⟩ := hB b hb
      exact (hM.degree_eq_one_iff b).mpr ⟨a, hab.symm⟩
    have hA_card : (A.filter (fun a => M.degree a = 1)).card = B.card := by
      rw [hM.toIsABMatching.card_matched_left_eq_right hdisj, hB_eq]
    have hA_eq : A.filter (fun a => M.degree a = 1) = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    intro a ha
    rw [← hA_eq] at ha
    exact (mem_filter.mp ha).2

/-- If `|B| ≤ |A|`, every maximum matching between `A` and `B` matches every vertex of `B`. -/
theorem IsMaxABMatching.forall_degree_eq_one_right_of_card_le {A B : Finset V}
    (hdisj : Disjoint A B) {M : SimpleGraph V} [DecidableRel M.Adj]
    (hM : IsMaxABMatching A B M) (hcard : B.card ≤ A.card) :
    ∀ b ∈ B, M.degree b = 1 :=
  hM.symm.forall_degree_eq_one_left_of_card_le hdisj.symm hcard

/-- Because `A ∪ B` is independent in `K` and `M` only adds edges between `A` and `B`,
`K` and `M` are edge-disjoint and degrees add pointwise in `K ⊔ M`. -/
theorem IsABMatching.degree_sup_eq_add [DecidableEq V] {K M : SimpleGraph V}
    [DecidableRel K.Adj] [DecidableRel M.Adj] [DecidableRel (K ⊔ M).Adj]
    {A B : Finset V} (hindep : K.IsIndepSet ((A ∪ B : Finset V) : Set V))
    (hM : IsABMatching A B M) (u : V) :
    (K ⊔ M).degree u = K.degree u + M.degree u := by
  have hunion : (K ⊔ M).neighborFinset u = K.neighborFinset u ∪ M.neighborFinset u := by
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  have hdisj : Disjoint (K.neighborFinset u) (M.neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro w hwK hwM
    have hKuw : K.Adj u w := (K.mem_neighborFinset u w).mp hwK
    have hMuw : M.Adj u w := (M.mem_neighborFinset u w).mp hwM
    rcases hM.edges_between u w hMuw with ⟨huA, hwB⟩ | ⟨huB, hwA⟩
    · exact hindep (mem_coe.mpr (mem_union_left B huA))
        (mem_coe.mpr (mem_union_right A hwB)) hKuw.ne hKuw
    · exact hindep (mem_coe.mpr (mem_union_right A huB))
        (mem_coe.mpr (mem_union_left B hwA)) hKuw.ne hKuw
  simp only [SimpleGraph.degree, hunion, card_union_of_disjoint hdisj]

end MatchingDegrees

end BipartiteMatching

/-! ## 3. Matching Theorem -/

section MatchingTheorem

private lemma completeBipartiteJoin_induce_eq {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (P : V → Prop) [DecidablePred P] :
    (completeBipartiteJoin K A B).induce { u : V | P u } =
      completeBipartiteJoin (K.induce { u : V | P u })
        (Finset.univ.filter (fun u : { u : V // P u } => u.1 ∈ A))
        (Finset.univ.filter (fun u : { u : V // P u } => u.1 ∈ B)) := by
  ext u v
  simp only [SimpleGraph.induce_adj, completeBipartiteJoin, mem_filter, mem_univ, true_and,
    ne_eq, Subtype.ext_iff]

/-- Inductive core of the Matching Theorem by strong induction on `n = Fintype.card V`. -/
private theorem matching_theorem_aux (hDel : MaxDegDeletionResiduePremise) :
    ∀ (n : ℕ), ∀ {V : Type u} [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ (K : SimpleGraph V) [DecidableRel K.Adj] (A B : Finset V),
        Disjoint A B →
        K.IsIndepSet ((A ∪ B : Finset V) : Set V) →
        ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj) (_ : DecidableRel (K ⊔ M).Adj),
          IsMaxABMatching A B M ∧
          SimpleGraph.residue (K ⊔ M) ≤ (completeBipartiteJoin K A B).indepNum := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hcard K _ A B hdisj hindep
    -- Reduce by symmetry to `A.card ≤ B.card`.
    have main : ∀ (A B : Finset V),
        Disjoint A B →
        K.IsIndepSet ((A ∪ B : Finset V) : Set V) →
        A.card ≤ B.card →
        ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj) (_ : DecidableRel (K ⊔ M).Adj),
          IsMaxABMatching A B M ∧
          SimpleGraph.residue (K ⊔ M) ≤ (completeBipartiteJoin K A B).indepNum := by
      intro A B hdisj hindep hAB_card
      -- Base case: `A = ∅`, so the empty matching `⊥` gives `H_M = T = K`.
      by_cases hA_empty : A = ∅
      · subst hA_empty
        let _ : DecidableRel (⊥ : SimpleGraph V).Adj := inferInstance
        let _ : DecidableRel (K ⊔ (⊥ : SimpleGraph V)).Adj := fun u v =>
          decidable_of_iff (K.Adj u v) (by simp)
        refine ⟨⊥, inferInstance, inferInstance, ?_, ?_⟩
        · refine ⟨⟨fun _ _ h => absurd h (by simp), fun _ _ _ h => absurd h (by simp)⟩,
            Or.inl (by simp)⟩
        · have hT : completeBipartiteJoin K ∅ B = K := completeBipartiteJoin_empty_left K B
          rw [hT]
          have hres_eq : SimpleGraph.residue (K ⊔ (⊥ : SimpleGraph V)) = SimpleGraph.residue K := by
            apply residue_eq_of_iso
            exact { toEquiv := Equiv.refl V, map_rel_iff' := by simp }
          rw [hres_eq]
          exact residue_le_indepNum_of_maxDegDeletion K hDel
      · -- Inductive step: `A.Nonempty`, hence `0 < A.card ≤ B.card` and `B.Nonempty`.
        have hA_ne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
        have hB_ne : B.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hA_ne.card_pos hAB_card)
        let U : Finset V := Finset.univ \ B
        have hU_ne : U.Nonempty := by
          obtain ⟨a₀, ha₀⟩ := hA_ne
          exact ⟨a₀, mem_sdiff.mpr ⟨mem_univ a₀, Finset.disjoint_left.mp hdisj ha₀⟩⟩
        let fixedDeg (u : V) : ℕ := if u ∈ A then K.degree u + 1 else K.degree u
        obtain ⟨v, hvU, hv_max⟩ := Finset.exists_max_image U fixedDeg hU_ne
        have hv_notB : v ∉ B := (mem_sdiff.mp hvU).2
        set p : ℕ := fixedDeg v
        have hp_pos : 0 < p := by
          obtain ⟨a₀, ha₀⟩ := hA_ne
          have ha₀U : a₀ ∈ U := mem_sdiff.mpr ⟨mem_univ a₀, Finset.disjoint_left.mp hdisj ha₀⟩
          have hle := hv_max a₀ ha₀U
          have ha₀_deg : fixedDeg a₀ = K.degree a₀ + 1 := ite_eq_left ha₀
          omega
        obtain ⟨b₀, hb₀B, hq_max⟩ := Finset.exists_max_image B (fun b => K.degree b) hB_ne
        set q : ℕ := K.degree b₀
        by_cases hpq : q + 1 ≤ p
        · -- Case 1: `p ≥ q + 1`. Delete `v ∉ B` (which has positive maximum degree `p` in `H_M`).
          let V' := { u : V // u ≠ v }
          have hcard_V' : Fintype.card V' < n := by
            have h := card_subtype_not_mem ({v} : Finset V)
            have hcard_eq : Fintype.card V' = Fintype.card { u : V // u ∉ ({v} : Finset V) } := by
              apply Fintype.card_congr
              exact { toFun := fun u => ⟨u.1, by simpa using u.2⟩
                      invFun := fun u => ⟨u.1, by simpa using u.2⟩
                      left_inv := fun _ => rfl
                      right_inv := fun _ => rfl }
            simp only [card_singleton] at h
            omega
          let K' : SimpleGraph V' := K.induce { u : V | u ≠ v }
          let A' : Finset V' := Finset.univ.filter (fun u : V' => u.1 ∈ A)
          let B' : Finset V' := Finset.univ.filter (fun u : V' => u.1 ∈ B)
          have hdisj' : Disjoint A' B' := by
            rw [Finset.disjoint_left]
            intro u huA huB
            exact Finset.disjoint_left.mp hdisj (mem_filter.mp huA).2 (mem_filter.mp huB).2
          have hindep' : K'.IsIndepSet ((A' ∪ B' : Finset V') : Set V') := by
            intro x hx y hy hxy
            have hxAB : x.1 ∈ A ∪ B := by
              rcases mem_union.mp (mem_coe.mp hx) with h | h
              · exact mem_union_left B (mem_filter.mp h).2
              · exact mem_union_right A (mem_filter.mp h).2
            have hyAB : y.1 ∈ A ∪ B := by
              rcases mem_union.mp (mem_coe.mp hy) with h | h
              · exact mem_union_left B (mem_filter.mp h).2
              · exact mem_union_right A (mem_filter.mp h).2
            exact hindep (mem_coe.mpr hxAB) (mem_coe.mpr hyAB) (fun h => hxy (Subtype.ext h))
          have hA'_card_eq : A'.card = (A.erase v).card := by
            rw [card_univ_filter_subtype]
            congr 1
            ext u
            simp [and_comm]
          have hB'_card_eq : B'.card = B.card := by
            rw [card_univ_filter_subtype]
            have hfilt : B.filter (fun u : V => u ≠ v) = B := by
              rw [Finset.filter_eq_self]
              intro u hu hEq
              exact hv_notB (hEq ▸ hu)
            rw [hfilt]
          have hA'B'_card : A'.card ≤ B'.card := by
            rw [hA'_card_eq, hB'_card_eq]
            exact (Finset.card_erase_le).trans hAB_card
          obtain ⟨M', hdecM', hdecKM', hM', hres'⟩ :=
            ih (Fintype.card V') hcard_V' rfl K' A' B' hdisj' hindep'
          have hM'_satA : ∀ a ∈ A', M'.degree a = 1 :=
            hM'.forall_degree_eq_one_left_of_card_le hdisj' hA'B'_card
          -- Extend `M'` to a maximum matching `M` on `V` such that `(K ⊔ M) - v ≃g K' ⊔ M'`.
          have hExt : ∃ M : SimpleGraph V,
              IsMaxABMatching A B M ∧
              (∀ x y : V', M.Adj x.1 y.1 ↔ M'.Adj x y) := by
            by_cases hvA : v ∈ A
            · -- Subcase 1b: `v ∈ A`, so `|A'| = |A| - 1 < |B'|`; match `v` to an unmatched `bstar ∈ B'`.
              have hlt_AB' : A'.card < B'.card := by
                have her := Finset.card_erase_add_one hvA
                omega
              have hex_unm : ∃ bstar ∈ B', M'.degree bstar = 0 := by
                by_contra hall
                push Not at hall
                have hB'_all : B'.filter (fun b => M'.degree b = 1) = B' := by
                  rw [Finset.filter_eq_self]
                  intro b hb
                  have hne0 := hall b hb
                  have hle1 := hM'.degree_le_one b
                  omega
                have hA'_all : A'.filter (fun a => M'.degree a = 1) = A' := by
                  rw [Finset.filter_eq_self]
                  exact hM'_satA
                have heq := hM'.toIsABMatching.card_matched_left_eq_right hdisj'
                rw [hA'_all, hB'_all] at heq
                omega
              obtain ⟨bstar, hbstar_B', hbstar_deg0⟩ := hex_unm
              have hbstar_B : bstar.1 ∈ B := (mem_filter.mp hbstar_B').2
              have hbstar_ne_v : bstar.1 ≠ v := bstar.2
              have hbstar_noM' : ∀ w : V', ¬ M'.Adj bstar w :=
                (hM'.toIsABMatching.degree_eq_zero_iff bstar).mp hbstar_deg0
              let M : SimpleGraph V :=
                { Adj := fun x y =>
                    (∃ (hx : x ≠ v) (hy : y ≠ v), M'.Adj ⟨x, hx⟩ ⟨y, hy⟩) ∨
                    (x = v ∧ y = bstar.1) ∨ (x = bstar.1 ∧ y = v)
                  symm := ⟨fun _ _ h => by
                    rcases h with ⟨hx, hy, hMxy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inl ⟨hy, hx, hMxy.symm⟩
                    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
                  loopless := ⟨fun x h => by
                    rcases h with ⟨hx, _, hMxx⟩ | ⟨rfl, hvb⟩ | ⟨hxb, hxv⟩
                    · exact M'.loopless.irrefl ⟨x, hx⟩ hMxx
                    · exact hbstar_ne_v hvb.symm
                    · exact hbstar_ne_v (hxb.symm.trans hxv)⟩ }
              refine ⟨M, ⟨⟨?_, ?_⟩, Or.inl ?_⟩, ?_⟩
              · intro x y hxy
                rcases hxy with ⟨hx, hy, hMxy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rcases hM'.edges_between ⟨x, hx⟩ ⟨y, hy⟩ hMxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact Or.inl ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
                  · exact Or.inr ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
                · exact Or.inl ⟨hvA, hbstar_B⟩
                · exact Or.inr ⟨hbstar_B, hvA⟩
              · intro x y z hxy hxz
                rcases hxy with ⟨hx1, hy1, hMxy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rcases hxz with ⟨hx2, hz2, hMxz⟩ | ⟨hxv, _⟩ | ⟨hxb, _⟩
                  · have hEq := hM'.unique_neighbor ⟨x, hx1⟩ ⟨y, hy1⟩ ⟨z, hz2⟩ hMxy hMxz
                    exact congrArg Subtype.val hEq
                  · exact absurd hxv hx1
                  · have hsub : (⟨x, hx1⟩ : V') = bstar := Subtype.ext hxb
                    exact absurd (hsub ▸ hMxy) (hbstar_noM' ⟨y, hy1⟩)
                · rcases hxz with ⟨hx2, _, _⟩ | ⟨_, rfl⟩ | ⟨hvb, _⟩
                  · exact absurd rfl hx2
                  · rfl
                  · exact absurd hvb.symm hbstar_ne_v
                · rcases hxz with ⟨hx2, hz2, hMxz⟩ | ⟨hbv, _⟩ | ⟨_, rfl⟩
                  · have hsub : (⟨bstar.1, hx2⟩ : V') = bstar := Subtype.ext rfl
                    exact absurd (hsub ▸ hMxz) (hbstar_noM' ⟨z, hz2⟩)
                  · exact absurd hbv hbstar_ne_v
                  · rfl
              · intro a ha
                by_cases hav : a = v
                · subst hav
                  exact ⟨bstar.1, hbstar_B, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
                · have ha' : (⟨a, hav⟩ : V') ∈ A' := mem_filter.mpr ⟨mem_univ _, ha⟩
                  obtain ⟨b', hab'⟩ := (hM'.toIsABMatching.degree_eq_one_iff ⟨a, hav⟩).mp (hM'_satA _ ha')
                  have hb'B : b'.1 ∈ B := by
                    rcases hM'.edges_between ⟨a, hav⟩ b' hab' with ⟨_, hb⟩ | ⟨haB, _⟩
                    · exact (mem_filter.mp hb).2
                    · exact absurd (mem_filter.mp haB).2 (Finset.disjoint_left.mp hdisj ha)
                  exact ⟨b'.1, hb'B, Or.inl ⟨hav, b'.2, hab'⟩⟩
              · intro x y
                simp only [M]
                constructor
                · rintro (⟨_, _, hMxy⟩ | ⟨hxv, _⟩ | ⟨_, hyv⟩)
                  · exact hMxy
                  · exact absurd hxv x.2
                  · exact absurd hyv y.2
                · intro hMxy
                  exact Or.inl ⟨x.2, y.2, hMxy⟩
            · -- Subcase 1a: `v ∉ A`; lift `M'` directly with `v` isolated in `M`.
              let M : SimpleGraph V :=
                { Adj := fun x y => ∃ (hx : x ≠ v) (hy : y ≠ v), M'.Adj ⟨x, hx⟩ ⟨y, hy⟩
                  symm := ⟨fun _ _ ⟨hx, hy, h⟩ => ⟨hy, hx, h.symm⟩⟩
                  loopless := ⟨fun x ⟨hx, _, h⟩ => M'.loopless.irrefl ⟨x, hx⟩ h⟩ }
              refine ⟨M, ⟨⟨?_, ?_⟩, Or.inl ?_⟩, ?_⟩
              · intro x y ⟨hx, hy, hMxy⟩
                rcases hM'.edges_between ⟨x, hx⟩ ⟨y, hy⟩ hMxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inl ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
                · exact Or.inr ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
              · intro x y z ⟨hx1, hy1, hMxy⟩ ⟨_, hz2, hMxz⟩
                exact congrArg Subtype.val (hM'.unique_neighbor ⟨x, hx1⟩ ⟨y, hy1⟩ ⟨z, hz2⟩ hMxy hMxz)
              · intro a ha
                have hav : a ≠ v := fun h => hvA (h ▸ ha)
                have ha' : (⟨a, hav⟩ : V') ∈ A' := mem_filter.mpr ⟨mem_univ _, ha⟩
                obtain ⟨b', hab'⟩ := (hM'.toIsABMatching.degree_eq_one_iff ⟨a, hav⟩).mp (hM'_satA _ ha')
                have hb'B : b'.1 ∈ B := by
                  rcases hM'.edges_between ⟨a, hav⟩ b' hab' with ⟨_, hb⟩ | ⟨haB, _⟩
                  · exact (mem_filter.mp hb).2
                  · exact absurd (mem_filter.mp haB).2 (Finset.disjoint_left.mp hdisj ha)
                exact ⟨b'.1, hb'B, ⟨hav, b'.2, hab'⟩⟩
              · intro x y
                simp only [M]
                exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x.2, y.2, h⟩⟩
          obtain ⟨M, hM, hM_ind⟩ := hExt
          let hdecM : DecidableRel M.Adj := Classical.decRel M.Adj
          let hdecH : DecidableRel (K ⊔ M).Adj := Classical.decRel (K ⊔ M).Adj
          let H : SimpleGraph V := K ⊔ M
          have hM_satA : ∀ a ∈ A, M.degree a = 1 :=
            hM.forall_degree_eq_one_left_of_card_le hdisj hAB_card
          have hH_deg_outB : ∀ u : V, u ∉ B → H.degree u = fixedDeg u := by
            intro u huB
            rw [hM.toIsABMatching.degree_sup_eq_add hindep u]
            dsimp only [fixedDeg]
            split_ifs with huA
            · rw [hM_satA u huA]
            · rw [hM.toIsABMatching.degree_eq_zero_of_not_mem huA huB, add_zero]
          have hH_deg_v : H.degree v = p := hH_deg_outB v hv_notB
          have hH_max : ∀ u : V, H.degree u ≤ H.degree v := by
            intro u
            rw [hH_deg_v]
            by_cases huB : u ∈ B
            · rw [hM.toIsABMatching.degree_sup_eq_add hindep u]
              have hK_le : K.degree u ≤ q := hq_max u huB
              have hM_le : M.degree u ≤ 1 := hM.toIsABMatching.degree_le_one u
              omega
            · rw [hH_deg_outB u huB]
              exact hv_max u (mem_sdiff.mpr ⟨mem_univ u, huB⟩)
          have hH_pos : 0 < H.degree v := hH_deg_v ▸ hp_pos
          have hdel_v : SimpleGraph.residue H ≤ SimpleGraph.residue (H.induce { u : V | u ≠ v }) :=
            hDel.apply H v hH_max hH_pos
          let iso : H.induce { u : V | u ≠ v } ≃g K' ⊔ M' :=
            { toEquiv := Equiv.refl V'
              map_rel_iff' := by
                intro x y
                change K.Adj x.1 y.1 ∨ M'.Adj x y ↔ K.Adj x.1 y.1 ∨ M.Adj x.1 y.1
                rw [hM_ind x y] }
          have hT'_le : (completeBipartiteJoin K' A' B').indepNum ≤
              (completeBipartiteJoin K A B).indepNum := by
            rw [← completeBipartiteJoin_induce_eq K A B (fun u : V => u ≠ v)]
            exact induce_indepNum_le (completeBipartiteJoin K A B) { u : V | u ≠ v }
          refine ⟨M, hdecM, hdecH, hM, ?_⟩
          calc
            SimpleGraph.residue H
                ≤ SimpleGraph.residue (H.induce { u : V | u ≠ v }) := hdel_v
            _ = SimpleGraph.residue (K' ⊔ M') := residue_eq_of_iso iso
            _ ≤ (completeBipartiteJoin K' A' B').indepNum := hres'
            _ ≤ (completeBipartiteJoin K A B).indepNum := hT'_le
        · -- Case 2: `p ≤ q` (hence `q ≥ 1`). Delete `S = { b ∈ B | deg_K(b) = q }`.
          have hp_le_q : p ≤ q := by omega
          have hq_pos : 0 < q := by omega
          let S : Finset V := B.filter (fun b => K.degree b = q)
          have hS_sub_B : S ⊆ B := Finset.filter_subset _ _
          have hb₀_S : b₀ ∈ S := mem_filter.mpr ⟨hb₀B, rfl⟩
          have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨b₀, hb₀_S⟩
          let V' := { u : V // u ∉ S }
          have hcard_V'_sum : Fintype.card V' + S.card = n := by
            simpa [V', hcard] using card_subtype_not_mem S
          have hcard_V' : Fintype.card V' < n := by omega
          let K' : SimpleGraph V' := K.induce { u : V | u ∉ S }
          let A' : Finset V' := Finset.univ.filter (fun u : V' => u.1 ∈ A)
          let B' : Finset V' := Finset.univ.filter (fun u : V' => u.1 ∈ B)
          have hdisj_AS : Disjoint A S := Disjoint.mono_right hS_sub_B hdisj
          have hdisj' : Disjoint A' B' := by
            rw [Finset.disjoint_left]
            intro u huA huB
            exact Finset.disjoint_left.mp hdisj (mem_filter.mp huA).2 (mem_filter.mp huB).2
          have hindep' : K'.IsIndepSet ((A' ∪ B' : Finset V') : Set V') := by
            intro x hx y hy hxy
            have hxAB : x.1 ∈ A ∪ B := by
              rcases mem_union.mp (mem_coe.mp hx) with h | h
              · exact mem_union_left B (mem_filter.mp h).2
              · exact mem_union_right A (mem_filter.mp h).2
            have hyAB : y.1 ∈ A ∪ B := by
              rcases mem_union.mp (mem_coe.mp hy) with h | h
              · exact mem_union_left B (mem_filter.mp h).2
              · exact mem_union_right A (mem_filter.mp h).2
            exact hindep (mem_coe.mpr hxAB) (mem_coe.mpr hyAB) (fun h => hxy (Subtype.ext h))
          have hA'_card : A'.card = A.card := by
            rw [card_univ_filter_subtype]
            have hfilt : A.filter (fun u : V => u ∉ S) = A := by
              rw [Finset.filter_eq_self]
              intro u hu
              exact Finset.disjoint_left.mp hdisj_AS hu
            rw [hfilt]
          have hB'_card_add : B'.card + S.card = B.card := by
            rw [card_univ_filter_subtype]
            have hfilt : B.filter (fun u : V => u ∉ S) = B \ S := by
              ext u
              simp [mem_sdiff]
            rw [hfilt, Finset.card_sdiff_add_card_eq_card hS_sub_B]
          obtain ⟨M', hdecM', hdecKM', hM', hres'⟩ :=
            ih (Fintype.card V') hcard_V' rfl K' A' B' hdisj' hindep'
          -- Count vertices of `A'` left unmatched by `M'`, and match them into `S₁ ⊆ S`.
          let A'_unm : Finset V' := A'.filter (fun a => M'.degree a = 0)
          let A'_mat : Finset V' := A'.filter (fun a => M'.degree a = 1)
          have hA'_split : A'_unm.card + A'_mat.card = A.card := by
            have hdisj_um : Disjoint A'_unm A'_mat := by
              rw [Finset.disjoint_left]
              intro a h0 h1
              have d0 := (mem_filter.mp h0).2
              have d1 := (mem_filter.mp h1).2
              omega
            have hunion : A'_unm ∪ A'_mat = A' := by
              ext a
              simp only [A'_unm, A'_mat, mem_union, mem_filter]
              constructor
              · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
              · intro ha
                have hle := hM'.toIsABMatching.degree_le_one a
                by_cases h0 : M'.degree a = 0
                · exact Or.inl ⟨ha, h0⟩
                · exact Or.inr ⟨ha, by omega⟩
            rw [← card_union_of_disjoint hdisj_um, hunion, hA'_card]
          have hA'_unm_le_S : A'_unm.card ≤ S.card := by
            rcases hM'.saturates with hsatA | hsatB
            · have hempty : A'_unm = ∅ := by
                ext a
                simp only [A'_unm, mem_filter, notMem_empty, iff_false, not_and]
                intro ha hdeg0
                obtain ⟨b, _, hab⟩ := hsatA a ha
                have h1 := (hM'.toIsABMatching.degree_eq_one_iff a).mpr ⟨b, hab⟩
                omega
              rw [hempty, card_empty]
              exact Nat.zero_le _
            · have hB'_all : B'.filter (fun b => M'.degree b = 1) = B' := by
                rw [Finset.filter_eq_self]
                intro b hb
                obtain ⟨a, _, hab⟩ := hsatB b hb
                exact (hM'.toIsABMatching.degree_eq_one_iff b).mpr ⟨a, hab.symm⟩
              have hmat_eq : A'_mat.card = B'.card := by
                dsimp only [A'_mat]
                rw [hM'.toIsABMatching.card_matched_left_eq_right hdisj', hB'_all]
              omega
          let A_unm : Finset V := A'_unm.map ⟨Subtype.val, Subtype.val_injective⟩
          have hA_unm_sub_A : A_unm ⊆ A := by
            intro a ha
            rcases mem_map.mp ha with ⟨a', ha', rfl⟩
            exact (mem_filter.mp (mem_filter.mp ha').1).2
          have hA_unm_card : A_unm.card = A'_unm.card := card_map _
          have hA_unm_le_S : A_unm.card ≤ S.card := hA_unm_card ▸ hA'_unm_le_S
          obtain ⟨S₁, hS₁_sub_S, hS₁_card⟩ := Finset.exists_subset_card_eq hA_unm_le_S
          have hcard_types : Fintype.card { a : V // a ∈ A_unm } =
              Fintype.card { s : V // s ∈ S₁ } := by
            rw [Fintype.card_coe, Fintype.card_coe, hS₁_card]
          let e : { a : V // a ∈ A_unm } ≃ { s : V // s ∈ S₁ } :=
            Fintype.equivOfCardEq hcard_types
          have hdisj_unm_S : Disjoint A_unm S := Disjoint.mono_left hA_unm_sub_A hdisj_AS
          have hdisj_unm_S₁ : Disjoint A_unm S₁ := Disjoint.mono_right hS₁_sub_S hdisj_unm_S
          have hA_unm_noM' : ∀ (a : V) (ha : a ∈ A_unm) (haS : a ∉ S) (w : V'),
              ¬ M'.Adj ⟨a, haS⟩ w := by
            intro a ha haS w
            rcases mem_map.mp ha with ⟨a', ha', ha_eq⟩
            have hsub : (⟨a, haS⟩ : V') = a' := Subtype.ext ha_eq.symm
            rw [hsub]
            exact (hM'.toIsABMatching.degree_eq_zero_iff a').mp (mem_filter.mp ha').2 w
          -- Build the extended matching `M` on `V` combining `M'` and the bijection `e : A_unm ≃ S₁`.
          let M : SimpleGraph V :=
            { Adj := fun x y =>
                (∃ (hx : x ∉ S) (hy : y ∉ S), M'.Adj ⟨x, hx⟩ ⟨y, hy⟩) ∨
                (∃ (hx : x ∈ A_unm) (hy : y ∈ S₁), (e ⟨x, hx⟩).1 = y) ∨
                (∃ (hy : y ∈ A_unm) (hx : x ∈ S₁), (e ⟨y, hy⟩).1 = x)
              symm := ⟨fun _ _ h => by
                rcases h with ⟨hx, hy, hMxy⟩ | ⟨hx, hy, heq⟩ | ⟨hy, hx, heq⟩
                · exact Or.inl ⟨hy, hx, hMxy.symm⟩
                · exact Or.inr (Or.inr ⟨hx, hy, heq⟩)
                · exact Or.inr (Or.inl ⟨hy, hx, heq⟩)⟩
              loopless := ⟨fun x h => by
                rcases h with ⟨hx, _, hMxx⟩ | ⟨hx1, hx2, _⟩ | ⟨hx1, hx2, _⟩
                · exact M'.loopless.irrefl ⟨x, hx⟩ hMxx
                · exact Finset.disjoint_left.mp hdisj_unm_S₁ hx1 hx2
                · exact Finset.disjoint_left.mp hdisj_unm_S₁ hx1 hx2⟩ }
          have hM : IsMaxABMatching A B M := by
            refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
            · intro x y hxy
              rcases hxy with ⟨hx, hy, hMxy⟩ | ⟨hx, hy, _⟩ | ⟨hy, hx, _⟩
              · rcases hM'.edges_between ⟨x, hx⟩ ⟨y, hy⟩ hMxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inl ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
                · exact Or.inr ⟨(mem_filter.mp h1).2, (mem_filter.mp h2).2⟩
              · exact Or.inl ⟨hA_unm_sub_A hx, hS_sub_B (hS₁_sub_S hy)⟩
              · exact Or.inr ⟨hS_sub_B (hS₁_sub_S hx), hA_unm_sub_A hy⟩
            · intro x y z hxy hxz
              rcases hxy with ⟨hx1, hy1, hMxy⟩ | ⟨hx1, hy1, hyeq⟩ | ⟨hy1, hx1, hxeq⟩
              · rcases hxz with ⟨_, hz2, hMxz⟩ | ⟨hx2, _, _⟩ | ⟨_, hx2, _⟩
                · exact congrArg Subtype.val
                    (hM'.unique_neighbor ⟨x, hx1⟩ ⟨y, hy1⟩ ⟨z, hz2⟩ hMxy hMxz)
                · exact absurd hMxy (hA_unm_noM' x hx2 hx1 ⟨y, hy1⟩)
                · exact absurd (hS₁_sub_S hx2) hx1
              · rcases hxz with ⟨hx2, hz2, hMxz⟩ | ⟨hx2, _, hzeq⟩ | ⟨_, hx2, _⟩
                · exact absurd hMxz (hA_unm_noM' x hx1 hx2 ⟨z, hz2⟩)
                · exact hyeq.symm.trans hzeq
                · exact absurd hx2 (Finset.disjoint_left.mp hdisj_unm_S₁ hx1)
              · rcases hxz with ⟨hx2, _, _⟩ | ⟨hx2, _, _⟩ | ⟨hz2, hx2, hzeq⟩
                · exact absurd (hS₁_sub_S hx1) hx2
                · exact absurd hx1 (Finset.disjoint_left.mp hdisj_unm_S₁ hx2)
                · have hsub : e ⟨y, hy1⟩ = e ⟨z, hz2⟩ := Subtype.ext (hxeq.trans hzeq.symm)
                  exact congrArg Subtype.val (e.injective hsub)
            · intro a ha
              by_cases ha_unm : a ∈ A_unm
              · refine ⟨(e ⟨a, ha_unm⟩).1, hS_sub_B (hS₁_sub_S (e ⟨a, ha_unm⟩).2), ?_⟩
                exact Or.inr (Or.inl ⟨ha_unm, (e ⟨a, ha_unm⟩).2, rfl⟩)
              · have haS : a ∉ S := Finset.disjoint_left.mp hdisj_AS ha
                have ha' : (⟨a, haS⟩ : V') ∈ A' := mem_filter.mpr ⟨mem_univ _, ha⟩
                have hne0 : M'.degree ⟨a, haS⟩ ≠ 0 := by
                  intro h0
                  have hmem : (⟨a, haS⟩ : V') ∈ A'_unm := mem_filter.mpr ⟨ha', h0⟩
                  exact ha_unm (mem_map.mpr ⟨⟨a, haS⟩, hmem, rfl⟩)
                have hdeg1 : M'.degree ⟨a, haS⟩ = 1 := by
                  have := hM'.toIsABMatching.degree_le_one ⟨a, haS⟩
                  omega
                obtain ⟨b', hab'⟩ := (hM'.toIsABMatching.degree_eq_one_iff ⟨a, haS⟩).mp hdeg1
                have hb'B : b'.1 ∈ B := by
                  rcases hM'.edges_between ⟨a, haS⟩ b' hab' with ⟨_, hb⟩ | ⟨haB, _⟩
                  · exact (mem_filter.mp hb).2
                  · exact absurd (mem_filter.mp haB).2 (Finset.disjoint_left.mp hdisj ha)
                exact ⟨b'.1, hb'B, Or.inl ⟨haS, b'.2, hab'⟩⟩
          let hdecM : DecidableRel M.Adj := Classical.decRel M.Adj
          let hdecH : DecidableRel (K ⊔ M).Adj := Classical.decRel (K ⊔ M).Adj
          let H : SimpleGraph V := K ⊔ M
          have hM_satA : ∀ a ∈ A, M.degree a = 1 :=
            hM.forall_degree_eq_one_left_of_card_le hdisj hAB_card
          -- Exact degree bounds in `H = K ⊔ M`:
          -- `S₁` has degree `q + 1`, `S \ S₁` has degree `q`, and every `u ∉ S` has degree `≤ q`.
          have hH_deg_S₁ : ∀ s ∈ S₁, H.degree s = q + 1 := by
            intro s hs₁
            have hsS : s ∈ S := hS₁_sub_S hs₁
            have hKs : K.degree s = q := (mem_filter.mp hsS).2
            have hMs : M.degree s = 1 := by
              rw [hM.toIsABMatching.degree_eq_one_iff]
              refine ⟨(e.symm ⟨s, hs₁⟩).1, Or.inr (Or.inr ⟨(e.symm ⟨s, hs₁⟩).2, hs₁, ?_⟩)⟩
              exact congrArg Subtype.val (e.apply_symm_apply ⟨s, hs₁⟩)
            rw [hM.toIsABMatching.degree_sup_eq_add hindep s, hKs, hMs]
          have hH_deg_S₀ : ∀ s ∈ S, s ∉ S₁ → H.degree s = q := by
            intro s hsS hs₁
            have hKs : K.degree s = q := (mem_filter.mp hsS).2
            have hMs : M.degree s = 0 := by
              rw [hM.toIsABMatching.degree_eq_zero_iff]
              intro w hsw
              rcases hsw with ⟨hs_notS, _, _⟩ | ⟨hs_unm, _, _⟩ | ⟨_, hs_S₁, _⟩
              · exact hs_notS hsS
              · exact Finset.disjoint_left.mp hdisj_unm_S hs_unm hsS
              · exact hs₁ hs_S₁
            rw [hM.toIsABMatching.degree_sup_eq_add hindep s, hKs, hMs, add_zero]
          have hH_deg_notS : ∀ u : V, u ∉ S → H.degree u ≤ q := by
            intro u huS
            rw [hM.toIsABMatching.degree_sup_eq_add hindep u]
            by_cases huB : u ∈ B
            · have hKle : K.degree u ≤ q := hq_max u huB
              have hKne : K.degree u ≠ q := fun hq_eq => huS (mem_filter.mpr ⟨huB, hq_eq⟩)
              have hMle : M.degree u ≤ 1 := hM.toIsABMatching.degree_le_one u
              omega
            · have huU : u ∈ U := mem_sdiff.mpr ⟨mem_univ u, huB⟩
              have hfle : fixedDeg u ≤ p := hv_max u huU
              by_cases huA : u ∈ A
              · have hM1 : M.degree u = 1 := hM_satA u huA
                have hf : fixedDeg u = K.degree u + 1 := ite_eq_left huA
                omega
              · have hM0 : M.degree u = 0 := hM.toIsABMatching.degree_eq_zero_of_not_mem huA huB
                have hf : fixedDeg u = K.degree u := ite_eq_right huA
                omega
          have hS_indep_H : H.IsIndepSet (S : Set V) := by
            intro x hx y hy hxy hHxy
            have hxB : x ∈ B := hS_sub_B (mem_coe.mp hx)
            have hyB : y ∈ B := hS_sub_B (mem_coe.mp hy)
            rcases (SimpleGraph.sup_adj K M x y).mp hHxy with hKxy | hMxy
            · exact hindep (mem_coe.mpr (mem_union_right A hxB))
                (mem_coe.mpr (mem_union_right A hyB)) hxy hKxy
            · rcases hM.edges_between x y hMxy with ⟨hxA, _⟩ | ⟨_, hyA⟩
              · exact Finset.disjoint_left.mp hdisj hxA hxB
              · exact Finset.disjoint_left.mp hdisj hyA hyB
          -- First delete `S₁` (independent set of uniform maximum degree `q + 1`).
          have hH_max_q1 : ∀ u : V, H.degree u ≤ q + 1 := by
            intro u
            by_cases huS : u ∈ S
            · by_cases huS₁ : u ∈ S₁
              · rw [hH_deg_S₁ u huS₁]
              · rw [hH_deg_S₀ u huS huS₁]; omega
            · have := hH_deg_notS u huS; omega
          have hS₁_indep_H : H.IsIndepSet (S₁ : Set V) :=
            fun x hx y hy hxy => hS_indep_H (mem_coe.mpr (hS₁_sub_S (mem_coe.mp hx)))
              (mem_coe.mpr (hS₁_sub_S (mem_coe.mp hy))) hxy
          let H₁ : SimpleGraph { u : V // u ∉ S₁ } := H.induce { u : V | u ∉ S₁ }
          have hdel1 : SimpleGraph.residue H ≤ SimpleGraph.residue H₁ :=
            residue_le_induce_compl_of_indep_maxDeg H S₁ (q + 1) (Nat.succ_pos q)
              hS₁_indep_H hH_deg_S₁ hH_max_q1 hDel
          -- Next delete `S₀' = { u ∈ H₁ | u ∈ S }` (independent set of uniform maximum degree `q`).
          let S₀' : Finset { u : V // u ∉ S₁ } := Finset.univ.filter (fun u => u.1 ∈ S)
          have hS₀'_indep : H₁.IsIndepSet (S₀' : Set { u : V // u ∉ S₁ }) := by
            intro x hx y hy hxy
            exact hS_indep_H (mem_coe.mpr (mem_filter.mp (mem_coe.mp hx)).2)
              (mem_coe.mpr (mem_filter.mp (mem_coe.mp hy)).2) (fun h => hxy (Subtype.ext h))
          have hS₀'_deg : ∀ s ∈ S₀', H₁.degree s = q := by
            intro s hs
            have hsS : s.1 ∈ S := (mem_filter.mp hs).2
            have hno : ∀ w : V, H.Adj s.1 w → w ∉ S₁ := by
              intro w hsw hwS₁
              have hwS : w ∈ S := hS₁_sub_S hwS₁
              exact hS_indep_H (mem_coe.mpr hsS) (mem_coe.mpr hwS) hsw.ne hsw
            calc
              H₁.degree s = H.degree s.1 :=
                induce_degree_eq_of_no_adj_outside H { u : V | u ∉ S₁ } s hno
              _ = q := hH_deg_S₀ s.1 hsS s.2
          have hH₁_max : ∀ u : { u : V // u ∉ S₁ }, H₁.degree u ≤ q := by
            intro u
            by_cases huS : u.1 ∈ S
            · rw [hS₀'_deg u (mem_filter.mpr ⟨mem_univ u, huS⟩)]
            · exact (induce_degree_le H { w : V | w ∉ S₁ } u).trans (hH_deg_notS u.1 huS)
          have hdel2 : SimpleGraph.residue H₁ ≤
              SimpleGraph.residue (H₁.induce { u : { u : V // u ∉ S₁ } | u ∉ S₀' }) :=
            residue_le_induce_compl_of_indep_maxDeg H₁ S₀' q hq_pos
              hS₀'_indep hS₀'_deg hH₁_max hDel
          -- After deleting `S₁` and `S \ S₁`, the remaining graph is isomorphic to `K' ⊔ M'`.
          let iso : H₁.induce { u : { u : V // u ∉ S₁ } | u ∉ S₀' } ≃g K' ⊔ M' :=
            { toFun := fun u => ⟨u.1.1, fun h => u.2 (mem_filter.mpr ⟨mem_univ _, h⟩)⟩
              invFun := fun u =>
                ⟨⟨u.1, fun h => u.2 (hS₁_sub_S h)⟩, fun h => u.2 (mem_filter.mp h).2⟩
              left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
              right_inv := fun _ => Subtype.ext rfl
              map_rel_iff' := by
                intro x y
                have hxS : x.1.1 ∉ S := fun h => x.2 (mem_filter.mpr ⟨mem_univ _, h⟩)
                have hyS : y.1.1 ∉ S := fun h => y.2 (mem_filter.mpr ⟨mem_univ _, h⟩)
                have hM_iff : M.Adj x.1.1 y.1.1 ↔ M'.Adj ⟨x.1.1, hxS⟩ ⟨y.1.1, hyS⟩ := by
                  simp only [M]
                  constructor
                  · rintro (⟨_, _, h⟩ | ⟨_, hy₁, _⟩ | ⟨_, hx₁, _⟩)
                    · exact h
                    · exact absurd (hS₁_sub_S hy₁) hyS
                    · exact absurd (hS₁_sub_S hx₁) hxS
                  · intro h
                    exact Or.inl ⟨hxS, hyS, h⟩
                change (K.Adj x.1.1 y.1.1 ∨ M'.Adj ⟨x.1.1, hxS⟩ ⟨y.1.1, hyS⟩) ↔
                  (K.Adj x.1.1 y.1.1 ∨ M.Adj x.1.1 y.1.1)
                rw [hM_iff] }
          have hT'_le : (completeBipartiteJoin K' A' B').indepNum ≤
              (completeBipartiteJoin K A B).indepNum := by
            rw [← completeBipartiteJoin_induce_eq K A B (fun u : V => u ∉ S)]
            exact induce_indepNum_le (completeBipartiteJoin K A B) { u : V | u ∉ S }
          refine ⟨M, hdecM, hdecH, hM, ?_⟩
          calc
            SimpleGraph.residue H
                ≤ SimpleGraph.residue H₁ := hdel1
            _ ≤ SimpleGraph.residue (H₁.induce { u : { u : V // u ∉ S₁ } | u ∉ S₀' }) := hdel2
            _ = SimpleGraph.residue (K' ⊔ M') := residue_eq_of_iso iso
            _ ≤ (completeBipartiteJoin K' A' B').indepNum := hres'
            _ ≤ (completeBipartiteJoin K A B).indepNum := hT'_le
    -- Apply symmetry between `A` and `B`.
    rcases le_total A.card B.card with hle | hle
    · exact main A B hdisj hindep hle
    · have hindep' : K.IsIndepSet ((B ∪ A : Finset V) : Set V) := by
        rwa [Finset.union_comm]
      obtain ⟨M, hdecM, hdecKM, hM, hres⟩ := main B A hdisj.symm hindep' hle
      refine ⟨M, hdecM, hdecKM, hM.symm, ?_⟩
      rwa [completeBipartiteJoin_comm] at hres

/--
**Matching Theorem (conditional only on
`MaxDegDeletionResiduePremise`):**
Let `K` be a finite simple graph with disjoint vertex sets `A, B` whose union induces an
edgeless graph in `K`, and let `T = completeBipartiteJoin K A B` add all possible edges
between `A` and `B`. Then there exists a matching `M` between `A` and `B` of size
`min |A| |B|` (`IsMaxABMatching A B M`) such that `SimpleGraph.residue (K ⊔ M) ≤ T.indepNum`.
-/
theorem matching_theorem_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (A B : Finset V) (hdisj : Disjoint A B)
    (hindep : K.IsIndepSet ((A ∪ B : Finset V) : Set V))
    (hDel : MaxDegDeletionResiduePremise) :
    ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj) (_ : DecidableRel (K ⊔ M).Adj),
      IsMaxABMatching A B M ∧
      SimpleGraph.residue (K ⊔ M) ≤ (completeBipartiteJoin K A B).indepNum :=
  matching_theorem_aux hDel (Fintype.card V) rfl K A B hdisj hindep

end MatchingTheorem

/-! ## 4. Induced-Matching Residue Inequality (IMR) and Full WOWII Conjecture 61 -/

section IMRAndWOWII61

/-- An independent set in `completeBipartiteJoin (removeBetween G A B) A B` misses `A` or `B`,
so its independence number equals `max α(G - A) α(G - B)`. -/
theorem completeBipartiteJoin_removeBetween_indepNum_eq_max
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V} (hdisj : Disjoint A B) :
    (completeBipartiteJoin (removeBetween G A B) A B).indepNum =
      max (G.induce { u : V | u ∉ A }).indepNum (G.induce { u : V | u ∉ B }).indepNum := by
  let K : SimpleGraph V := removeBetween G A B
  let T : SimpleGraph V := completeBipartiteJoin K A B
  apply le_antisymm
  · obtain ⟨I, hI⟩ := T.exists_isNIndepSet_indepNum
    have hdisj_or : Disjoint I A ∨ Disjoint I B := by
      by_contra hboth
      push Not at hboth
      obtain ⟨hIA, hIB⟩ := hboth
      rw [Finset.not_disjoint_iff] at hIA hIB
      obtain ⟨a, haI, haA⟩ := hIA
      obtain ⟨b, hbI, hbB⟩ := hIB
      have hab : a ≠ b := fun h => Finset.disjoint_left.mp hdisj haA (h ▸ hbB)
      have hadj : T.Adj a b :=
        (completeBipartiteJoin_adj_of_disjoint K hdisj a b).mpr (Or.inr (Or.inl ⟨haA, hbB⟩))
      exact hI.isIndepSet (mem_coe.mpr haI) (mem_coe.mpr hbI) hab hadj
    rcases hdisj_or with hIA | hIB
    · apply le_max_of_le_left
      let I' : Finset { u : V // u ∉ A } := Finset.univ.filter (fun u => u.1 ∈ I)
      have hI'_card : I'.card = I.card := by
        rw [card_univ_filter_subtype]
        have hfilt : I.filter (fun u : V => u ∉ A) = I := by
          rw [Finset.filter_eq_self]
          exact fun u hu => Finset.disjoint_left.mp hIA hu
        rw [hfilt]
      have hI'_indep : (G.induce { u : V | u ∉ A }).IsIndepSet (I' : Set { u : V // u ∉ A }) := by
        intro x hx y hy hxy hGxy
        have hxI : x.1 ∈ I := (mem_filter.mp (mem_coe.mp hx)).2
        have hyI : y.1 ∈ I := (mem_filter.mp (mem_coe.mp hy)).2
        have hKxy : K.Adj x.1 y.1 := by
          refine ⟨hGxy, ?_⟩
          rintro (⟨hxA, _⟩ | ⟨_, hyA⟩)
          · exact x.2 hxA
          · exact y.2 hyA
        have hTxy : T.Adj x.1 y.1 :=
          (completeBipartiteJoin_adj_of_disjoint K hdisj x.1 y.1).mpr (Or.inl hKxy)
        exact hI.isIndepSet (mem_coe.mpr hxI) (mem_coe.mpr hyI) (fun h => hxy (Subtype.ext h)) hTxy
      rw [← hI.card_eq, ← hI'_card]
      exact hI'_indep.card_le_indepNum
    · apply le_max_of_le_right
      let I' : Finset { u : V // u ∉ B } := Finset.univ.filter (fun u => u.1 ∈ I)
      have hI'_card : I'.card = I.card := by
        rw [card_univ_filter_subtype]
        have hfilt : I.filter (fun u : V => u ∉ B) = I := by
          rw [Finset.filter_eq_self]
          exact fun u hu => Finset.disjoint_left.mp hIB hu
        rw [hfilt]
      have hI'_indep : (G.induce { u : V | u ∉ B }).IsIndepSet (I' : Set { u : V // u ∉ B }) := by
        intro x hx y hy hxy hGxy
        have hxI : x.1 ∈ I := (mem_filter.mp (mem_coe.mp hx)).2
        have hyI : y.1 ∈ I := (mem_filter.mp (mem_coe.mp hy)).2
        have hKxy : K.Adj x.1 y.1 := by
          refine ⟨hGxy, ?_⟩
          rintro (⟨_, hyB⟩ | ⟨hxB, _⟩)
          · exact y.2 hyB
          · exact x.2 hxB
        have hTxy : T.Adj x.1 y.1 :=
          (completeBipartiteJoin_adj_of_disjoint K hdisj x.1 y.1).mpr (Or.inl hKxy)
        exact hI.isIndepSet (mem_coe.mpr hxI) (mem_coe.mpr hyI) (fun h => hxy (Subtype.ext h)) hTxy
      rw [← hI.card_eq, ← hI'_card]
      exact hI'_indep.card_le_indepNum
  · apply max_le
    · obtain ⟨I, hI⟩ := (G.induce { u : V | u ∉ A }).exists_isNIndepSet_indepNum
      let J : Finset V := I.map ⟨Subtype.val, Subtype.val_injective⟩
      have hJ : T.IsIndepSet (J : Set V) := by
        intro x hx y hy hxy hTxy
        rw [mem_coe, mem_map] at hx hy
        rcases hx with ⟨x0, hx0, rfl⟩
        rcases hy with ⟨y0, hy0, rfl⟩
        rcases (completeBipartiteJoin_adj_of_disjoint K hdisj x0.1 y0.1).mp hTxy with
            hKxy | ⟨hxA, _⟩ | ⟨_, hyA⟩
        · exact hI.isIndepSet (mem_coe.mpr hx0) (mem_coe.mpr hy0)
            (fun h => hxy (congrArg Subtype.val h)) hKxy.1
        · exact x0.2 hxA
        · exact y0.2 hyA
      have hcard : J.card = (G.induce { u : V | u ∉ A }).indepNum := by
        rw [card_map, hI.card_eq]
      rw [← hcard]
      exact hJ.card_le_indepNum
    · obtain ⟨I, hI⟩ := (G.induce { u : V | u ∉ B }).exists_isNIndepSet_indepNum
      let J : Finset V := I.map ⟨Subtype.val, Subtype.val_injective⟩
      have hJ : T.IsIndepSet (J : Set V) := by
        intro x hx y hy hxy hTxy
        rw [mem_coe, mem_map] at hx hy
        rcases hx with ⟨x0, hx0, rfl⟩
        rcases hy with ⟨y0, hy0, rfl⟩
        rcases (completeBipartiteJoin_adj_of_disjoint K hdisj x0.1 y0.1).mp hTxy with
            hKxy | ⟨_, hyB⟩ | ⟨hxB, _⟩
        · exact hI.isIndepSet (mem_coe.mpr hx0) (mem_coe.mpr hy0)
            (fun h => hxy (congrArg Subtype.val h)) hKxy.1
        · exact y0.2 hyB
        · exact x0.2 hxB
      have hcard : J.card = (G.induce { u : V | u ∉ B }).indepNum := by
        rw [card_map, hI.card_eq]
      rw [← hcard]
      exact hJ.card_le_indepNum

/--
**Induced-Matching Residue Inequality (IMR, conditional only on `MaxDegDeletionResiduePremise`):**
For every finite simple graph `G` and every induced matching `IM : InducedMatching G k`,
`SimpleGraph.residue G ≤ max α(G - IM.A) α(G - IM.B)`.
-/
theorem imr_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (IM : InducedMatching G k)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G ≤
      max (G.induce { u : V | u ∉ IM.A }).indepNum
          (G.induce { u : V | u ∉ IM.B }).indepNum := by
  let K : SimpleGraph V := removeBetween G IM.A IM.B
  let _ : DecidableRel K.Adj := fun u v =>
    decidable_of_iff (G.Adj u v ∧ ¬ ((u ∈ IM.A ∧ v ∈ IM.B) ∨ (u ∈ IM.B ∧ v ∈ IM.A))) Iff.rfl
  have hK_indep : K.IsIndepSet ((IM.A ∪ IM.B : Finset V) : Set V) := by
    intro x hx y hy hxy hKxy
    rcases mem_union.mp (mem_coe.mp hx) with hxA | hxB <;>
      rcases mem_union.mp (mem_coe.mp hy) with hyA | hyB
    · exact IM.A_indep (mem_coe.mpr hxA) (mem_coe.mpr hyA) hxy hKxy.1
    · exact hKxy.2 (Or.inl ⟨hxA, hyB⟩)
    · exact hKxy.2 (Or.inr ⟨hxB, hyA⟩)
    · exact IM.B_indep (mem_coe.mpr hxB) (mem_coe.mpr hyB) hxy hKxy.1
  obtain ⟨M, hdecM, hdecKM, hM, hres⟩ :=
    matching_theorem_of_maxDegDeletion K IM.A IM.B IM.disjoint_AB hK_indep hDel
  have hM_satA : ∀ a ∈ IM.A, M.degree a = 1 :=
    hM.forall_degree_eq_one_left_of_card_le IM.disjoint_AB (by rw [IM.A_card, IM.B_card])
  have hM_satB : ∀ b ∈ IM.B, M.degree b = 1 :=
    hM.forall_degree_eq_one_right_of_card_le IM.disjoint_AB (by rw [IM.A_card, IM.B_card])
  -- Removing the induced matching drops degrees in `IM.A ∪ IM.B` by 1 and leaves others fixed;
  -- adding `M` restores every degree identically, so `(K ⊔ M).degree u = G.degree u`.
  have hdeg_eq : ∀ u : V, (K ⊔ M).degree u = G.degree u := by
    intro u
    rw [hM.toIsABMatching.degree_sup_eq_add hK_indep u]
    by_cases huA : u ∈ IM.A
    · rw [hM_satA u huA]
      rw [IM.A_eq] at huA
      rcases mem_image.mp huA with ⟨i, _, rfl⟩
      have hai_A : IM.a i ∈ IM.A := by rw [IM.A_eq]; exact mem_image_of_mem _ (mem_univ i)
      have hbi_B : IM.b i ∈ IM.B := by rw [IM.B_eq]; exact mem_image_of_mem _ (mem_univ i)
      have hbi_notK : IM.b i ∉ K.neighborFinset (IM.a i) := by
        rw [SimpleGraph.mem_neighborFinset]
        exact fun h => h.2 (Or.inl ⟨hai_A, hbi_B⟩)
      have hnb : G.neighborFinset (IM.a i) = insert (IM.b i) (K.neighborFinset (IM.a i)) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, mem_insert]
        constructor
        · intro haw
          by_cases hwB : w ∈ IM.B
          · rw [IM.B_eq] at hwB
            rcases mem_image.mp hwB with ⟨j, _, rfl⟩
            have hij : i = j := (IM.adj_iff i j).mp haw
            exact Or.inl (congrArg IM.b hij.symm)
          · refine Or.inr ⟨haw, ?_⟩
            rintro (⟨_, hwB'⟩ | ⟨hai_B, _⟩)
            · exact hwB hwB'
            · exact Finset.disjoint_left.mp IM.disjoint_AB hai_A hai_B
        · rintro (rfl | hKaw)
          · exact (IM.adj_iff i i).mpr rfl
          · exact hKaw.1
      simp only [SimpleGraph.degree, hnb, card_insert_of_notMem hbi_notK]
    · by_cases huB : u ∈ IM.B
      · rw [hM_satB u huB]
        rw [IM.B_eq] at huB
        rcases mem_image.mp huB with ⟨i, _, rfl⟩
        have hai_A : IM.a i ∈ IM.A := by rw [IM.A_eq]; exact mem_image_of_mem _ (mem_univ i)
        have hbi_B : IM.b i ∈ IM.B := by rw [IM.B_eq]; exact mem_image_of_mem _ (mem_univ i)
        have hai_notK : IM.a i ∉ K.neighborFinset (IM.b i) := by
          rw [SimpleGraph.mem_neighborFinset]
          exact fun h => h.2 (Or.inr ⟨hbi_B, hai_A⟩)
        have hnb : G.neighborFinset (IM.b i) = insert (IM.a i) (K.neighborFinset (IM.b i)) := by
          ext w
          simp only [SimpleGraph.mem_neighborFinset, mem_insert]
          constructor
          · intro hbw
            by_cases hwA : w ∈ IM.A
            · rw [IM.A_eq] at hwA
              rcases mem_image.mp hwA with ⟨j, _, rfl⟩
              have hji : j = i := (IM.adj_iff j i).mp hbw.symm
              exact Or.inl (congrArg IM.a hji)
            · refine Or.inr ⟨hbw, ?_⟩
              rintro (⟨hbi_A, _⟩ | ⟨_, hwA'⟩)
              · exact Finset.disjoint_right.mp IM.disjoint_AB hbi_B hbi_A
              · exact hwA hwA'
          · rintro (rfl | hKbw)
            · exact ((IM.adj_iff i i).mpr rfl).symm
            · exact hKbw.1
        simp only [SimpleGraph.degree, hnb, card_insert_of_notMem hai_notK]
      · rw [hM.toIsABMatching.degree_eq_zero_of_not_mem huA huB, add_zero]
        have hnb : K.neighborFinset u = G.neighborFinset u := by
          ext w
          simp only [SimpleGraph.mem_neighborFinset]
          constructor
          · exact fun h => h.1
          · intro huw
            refine ⟨huw, ?_⟩
            rintro (⟨h, _⟩ | ⟨h, _⟩)
            · exact huA h
            · exact huB h
        simp only [SimpleGraph.degree, hnb]
  have hres_eq : SimpleGraph.residue (K ⊔ M) = SimpleGraph.residue G :=
    residue_eq_of_degree_eq hdeg_eq
  rw [← hres_eq]
  exact hres.trans_eq (completeBipartiteJoin_removeBetween_indepNum_eq_max G IM.disjoint_AB)

/-- Exact IMR premise expected by `WOWII61.PackingForest.wowii61_of_imr_premise`. -/
theorem imr_premise_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hDel : MaxDegDeletionResiduePremise) :
    ∀ M : InducedMatching G ((G.diam + 2) / 3),
      SimpleGraph.residue G ≤
        max (G.induce { u : V | u ∉ M.A }).indepNum
            (G.induce { u : V | u ∉ M.B }).indepNum :=
  fun M => imr_of_maxDegDeletion G M hDel

/-- **Full WOWII Conjecture 61 (`ℕ`-valued) for every nontrivial finite connected graph,**
assuming only `WOWII61.PackingBound.MaxDegDeletionResiduePremise`. -/
theorem wowii61_of_maxDegDeletion_nontrivial
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize :=
  wowii61_of_imr_premise G hconn (imr_premise_of_maxDegDeletion G hDel)

/-- **Full WOWII Conjecture 61 (`ℕ`-valued) for EVERY finite connected graph**
(including 1-vertex graphs), assuming only `WOWII61.PackingBound.MaxDegDeletionResiduePremise`. -/
theorem wowii61_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  have : Nonempty V := hconn.nonempty
  rcases subsingleton_or_nontrivial V with hsub | hnontriv
  · have hD0 : G.diam = 0 := SimpleGraph.diam_eq_zero.mpr (Or.inr hsub)
    exact wowii61_of_small_diam_conditional G hconn (Or.inl hD0)
      (residue_le_indepNum_of_maxDegDeletion G hDel)
  · exact wowii61_of_maxDegDeletion_nontrivial G hconn hDel

end IMRAndWOWII61

end WOWII61.MatchingResidue
