module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import WOWII61.Defs

/-!
# Packing, Geodesic Distance, and Induced-Forest Bounds for WOWII Conjecture 61

This module formalizes unconditional core/distance/packing theorems directly against the
exact upstream definitions `SimpleGraph.largestInducedForestSize`, `SimpleGraph.diam`,
`SimpleGraph.indepNum`, and `SimpleGraph.residue`:

1. **Star-Packing Forest Bound (Lemma 1)**:
   For any 3-packing `W` and disjoint independent set `I`, `G[I ∪ W]` is acyclic, so
   `α(G - W) + |W| ≤ f(G)` (`isAcyclic_induce_union_of_isThreePacking`,
   `indepNum_compl_add_card_le_largestInducedForestSize`).
2. **Diametral Geodesic Extraction**:
   Every finite connected graph has a diametral geodesic `p : Fin (G.diam + 1) → V`
   with `G.dist (p i) (p j) = j - i` for `i ≤ j` (`exists_diametral_geodesic`).
3. **Greedy Diametral 3-Packing Bound (Lemma 2)**:
   Unconditionally for every finite connected graph `G`,
   `α(G) + (G.diam + 3) / 4 ≤ f(G)` (`indepNum_add_ceil_diam_div_four_le_largestInducedForestSize`).
4. **Small-Diameter WOWII #61 (Corollary 4)**:
   For `G.diam ∈ {0, 1, 2, 3, 5, 6, 9}`, unconditionally `α(G) + (G.diam + 2) / 3 ≤ f(G)`,
   and conditionally on the explicit FMS premise `residue G ≤ α(G)`,
   `residue G + (G.diam + 2) / 3 ≤ f(G)`.
5. **Monotone 3-Packings & IMR Reduction (Theorem 5)**:
   Every nontrivial finite connected graph has `k + 1` monotone 3-packings (`k = (D + 2) / 3`)
   and an induced matching `(A, B)` of size `k` along a diametral geodesic such that
   `max (α(G - A)) (α(G - B)) + k ≤ f(G)`. Thus IMR (or the weaker Monotone IMR)
   unconditionally implies `residue G + (G.diam + 2) / 3 ≤ f(G)`.
6. **Exact `D = 4` Tight-Boundary Anatomy (Theorem 7)**:
   If `G` is connected with `f(G) ≤ α(G) + 1`, then for every maximum independent set `I`
   and every pair `(u, w)` at distance 4: `u ∈ I`, `w ∈ I`, `N(u)` and `N(w)` are disjoint
   with no edges between them, and every `a ∈ N(u), b ∈ N(w)` share at least 2 common
   neighbors in `I`.
-/

@[expose] public section

namespace WOWII61.PackingForest

open SimpleGraph Finset

variable {V : Type*}

/-! ## 1. Star-Packing Forest Bound (Lemma 1) -/

/-- A subset `W` is a *3-packing* in `G` if distinct vertices of `W` have extended distance ≥ 3. -/
def IsThreePacking (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ w ∈ W, u ≠ w → (3 : ℕ∞) ≤ G.edist u w

theorem IsThreePacking.isIndepSet {G : SimpleGraph V} {W : Finset V} (hW : IsThreePacking G W) :
    G.IsIndepSet (W : Set V) := by
  intro u hu w hw huw hadj
  have h3 : (3 : ℕ∞) ≤ G.edist u w := hW u (mem_coe.mp hu) w (mem_coe.mp hw) huw
  have h1 : G.edist u w = 1 := SimpleGraph.edist_eq_one_iff_adj.mpr hadj
  rw [h1] at h3
  exact absurd h3 (by decide)

/-- If `I` is independent and `W` is a 3-packing in `G`, then `G[I ∪ W]` is acyclic (a forest). -/
theorem isAcyclic_induce_union_of_isThreePacking [DecidableEq V]
    (G : SimpleGraph V) {I W : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hW : IsThreePacking G W) :
    (G.induce ((I ∪ W : Finset V) : Set V)).IsAcyclic := by
  have hW_indep : G.IsIndepSet (W : Set V) := hW.isIndepSet
  intro u c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hnodup : c.edges.Nodup := hc.edges_nodup
  match c with
  | .nil => simp at hlen
  | .cons _ .nil => simp at hlen
  | .cons _ (.cons _ .nil) => simp at hlen
  | .cons (u := a) (v := b) h1 (.cons (v := d) h2 (.cons (v := e) h3 rest)) =>
    simp only [Walk.edges_cons, List.nodup_cons, List.mem_cons, not_or] at hnodup
    have hab_ne_bd : s(a, b) ≠ s(b, d) := hnodup.1.1
    have hbd_ne_de : s(b, d) ≠ s(d, e) := hnodup.2.1.1
    have had : a.1 ≠ d.1 := by
      intro h
      have heq : a = d := Subtype.ext h
      subst heq
      exact hab_ne_bd Sym2.eq_swap
    have hbe : b.1 ≠ e.1 := by
      intro h
      have heq : b = e := Subtype.ext h
      subst heq
      exact hbd_ne_de Sym2.eq_swap
    have h1' : G.Adj a.1 b.1 := h1
    have h2' : G.Adj b.1 d.1 := h2
    have h3' : G.Adj d.1 e.1 := h3
    by_cases hbI : b.1 ∈ I
    · have ha_notI : a.1 ∉ I := fun h => hI (mem_coe.mpr h) (mem_coe.mpr hbI) h1'.ne h1'
      have hd_notI : d.1 ∉ I := fun h => hI (mem_coe.mpr hbI) (mem_coe.mpr h) h2'.ne h2'
      have haW : a.1 ∈ W := (mem_union.mp (mem_coe.mp a.2)).resolve_left ha_notI
      have hdW : d.1 ∈ W := (mem_union.mp (mem_coe.mp d.2)).resolve_left hd_notI
      have h3le : (3 : ℕ∞) ≤ G.edist a.1 d.1 := hW a.1 haW d.1 hdW had
      have hle2 : G.edist a.1 d.1 ≤ (2 : ℕ∞) := by
        calc
          G.edist a.1 d.1 ≤ G.edist a.1 b.1 + G.edist b.1 d.1 := G.edist_triangle
          _ = (1 : ℕ∞) + 1 := by
            rw [SimpleGraph.edist_eq_one_iff_adj.mpr h1',
              SimpleGraph.edist_eq_one_iff_adj.mpr h2']
          _ = 2 := rfl
      exact absurd (h3le.trans hle2) (by decide)
    · have hbW : b.1 ∈ W := (mem_union.mp (mem_coe.mp b.2)).resolve_left hbI
      have hd_notW : d.1 ∉ W := fun h => hW_indep (mem_coe.mpr hbW) (mem_coe.mpr h) h2'.ne h2'
      have hdI : d.1 ∈ I := (mem_union.mp (mem_coe.mp d.2)).resolve_right hd_notW
      have he_notI : e.1 ∉ I := fun h => hI (mem_coe.mpr hdI) (mem_coe.mpr h) h3'.ne h3'
      have heW : e.1 ∈ W := (mem_union.mp (mem_coe.mp e.2)).resolve_left he_notI
      have h3le : (3 : ℕ∞) ≤ G.edist b.1 e.1 := hW b.1 hbW e.1 heW hbe
      have hle2 : G.edist b.1 e.1 ≤ (2 : ℕ∞) := by
        calc
          G.edist b.1 e.1 ≤ G.edist b.1 d.1 + G.edist d.1 e.1 := G.edist_triangle
          _ = (1 : ℕ∞) + 1 := by
            rw [SimpleGraph.edist_eq_one_iff_adj.mpr h2',
              SimpleGraph.edist_eq_one_iff_adj.mpr h3']
          _ = 2 := rfl
      exact absurd (h3le.trans hle2) (by decide)

theorem card_le_largestInducedForestSize [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {S : Finset V} (hS : (G.induce (S : Set V)).IsAcyclic) :
    S.card ≤ G.largestInducedForestSize := by
  apply le_csSup
  · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨S, hS, rfl⟩

/-- **Star-Packing Forest Bound (subset form):** `|I| + |W| ≤ f(G)`. -/
theorem card_indep_add_threePacking_le_largestInducedForestSize [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {I W : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hW : IsThreePacking G W) (hdisj : Disjoint I W) :
    I.card + W.card ≤ G.largestInducedForestSize := by
  have hacyc := isAcyclic_induce_union_of_isThreePacking G hI hW
  have hle := card_le_largestInducedForestSize G hacyc
  rwa [card_union_of_disjoint hdisj] at hle

/-- **Star-Packing Forest Bound (Lemma 1):** `α(G - W) + |W| ≤ f(G)` for every 3-packing `W`. -/
theorem indepNum_compl_add_card_le_largestInducedForestSize [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (hW : IsThreePacking G W) :
    (G.induce { u : V | u ∉ W }).indepNum + W.card ≤ G.largestInducedForestSize := by
  obtain ⟨S, hS⟩ := (G.induce { u : V | u ∉ W }).exists_isNIndepSet_indepNum
  let I : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
  have hI_indep : G.IsIndepSet (I : Set V) := by
    intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases hb with ⟨b0, hb0, rfl⟩
    have hne : a0 ≠ b0 := fun h => hab (congrArg Subtype.val h)
    exact hS.isIndepSet (mem_coe.mpr ha0) (mem_coe.mpr hb0) hne
  have hdisj : Disjoint I W := by
    rw [Finset.disjoint_left]
    intro u hu
    rcases mem_map.mp hu with ⟨⟨u0, hu0⟩, _, rfl⟩
    exact hu0
  have hcard : I.card = (G.induce { u : V | u ∉ W }).indepNum := by
    rw [card_map, hS.card_eq]
  rw [← hcard]
  exact card_indep_add_threePacking_le_largestInducedForestSize G hI_indep hW hdisj

/-! ## 2. Diametral Geodesic Extraction -/

private lemma dist_getVert_le_sub {G : SimpleGraph V} (hconn : G.Connected) {u v : V}
    (w : G.Walk u v) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ w.length → G.dist (w.getVert i) (w.getVert j) ≤ j - i := by
  intro i j hij hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hstep : G.Adj (w.getVert (i + k)) (w.getVert (i + k + 1)) := by
      have := w.adj_getVert_succ (i := i + k) (by omega)
      simpa [Nat.add_assoc] using this
    have htri : G.dist (w.getVert i) (w.getVert (i + k + 1)) ≤
        G.dist (w.getVert i) (w.getVert (i + k)) + G.dist (w.getVert (i + k)) (w.getVert (i + k + 1)) :=
      (hconn (w.getVert i) (w.getVert (i + k))).dist_triangle_left (w.getVert (i + k + 1))
    have hdist1 : G.dist (w.getVert (i + k)) (w.getVert (i + k + 1)) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hstep
    have ih' := ih (by omega) (by omega)
    rw [← Nat.add_assoc]
    omega

/-- Every finite connected graph admits a diametral geodesic `p : Fin (G.diam + 1) → V`
whose induced pairwise distances equal `|j - i|`. -/
theorem exists_diametral_geodesic [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hconn : G.Connected) :
    ∃ p : Fin (G.diam + 1) → V,
      (∀ i : Fin G.diam, G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i j : Fin (G.diam + 1), i.val ≤ j.val → G.dist (p i) (p j) = j.val - i.val) ∧
      (∀ i j : Fin (G.diam + 1), i.val ≤ j.val →
        G.edist (p i) (p j) = ((j.val - i.val : ℕ) : ℕ∞)) := by
  have hne_top : G.ediam ≠ ⊤ := by
    obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
    rw [← huv, SimpleGraph.edist_ne_top_iff_reachable]
    exact hconn u v
  obtain ⟨u, v, huv_edist⟩ := G.exists_edist_eq_ediam_of_ne_top hne_top
  have huv_dist : G.dist u v = G.diam := by
    have hcoe : (G.dist u v : ℕ∞) = G.ediam := by
      rw [(hconn u v).coe_dist_eq_edist, huv_edist]
    simpa [SimpleGraph.diam] using congrArg ENat.toNat hcoe
  obtain ⟨w, _, hw_len⟩ := hconn.exists_path_of_dist u v
  have hw_diam : w.length = G.diam := hw_len.trans huv_dist
  let p : Fin (G.diam + 1) → V := fun i => w.getVert i.val
  have hp_adj : ∀ i : Fin G.diam, G.Adj (p i.castSucc) (p i.succ) := by
    intro i
    simpa [p] using w.adj_getVert_succ (i := i.val) (hw_diam.symm ▸ i.isLt)
  have hp_dist : ∀ i j : Fin (G.diam + 1), i.val ≤ j.val → G.dist (p i) (p j) = j.val - i.val := by
    intro i j hij
    have h0i : G.dist u (p i) ≤ i.val := by
      simpa [p, Walk.getVert_zero] using
        dist_getVert_le_sub hconn w (i := 0) (j := i.val) (Nat.zero_le _) (by omega)
    have hij_le : G.dist (p i) (p j) ≤ j.val - i.val :=
      dist_getVert_le_sub hconn w hij (by omega)
    have hjD : G.dist (p j) v ≤ G.diam - j.val := by
      have h := dist_getVert_le_sub hconn w (i := j.val) (j := w.length) (by omega) le_rfl
      rw [Walk.getVert_length, hw_diam] at h
      exact h
    have htri1 : G.dist u v ≤ G.dist u (p i) + G.dist (p i) v :=
      (hconn u (p i)).dist_triangle_left v
    have htri2 : G.dist (p i) v ≤ G.dist (p i) (p j) + G.dist (p j) v :=
      (hconn (p i) (p j)).dist_triangle_left v
    omega
  refine ⟨p, hp_adj, hp_dist, fun i j hij => ?_⟩
  rw [← (hconn (p i) (p j)).coe_dist_eq_edist, hp_dist i j hij]

/-! ## 3. Greedy Diametral 3-Packing Bound (Lemma 2) & Small-Diameter WOWII #61 (Corollary 4) -/

private def greedyIdx (p : Fin (D + 1) → V) (I : Finset V) [DecidableEq V] : ℕ → ℕ
  | 0 => if h : 0 < D + 1 then (if p ⟨0, h⟩ ∈ I then 1 else 0) else 0
  | t + 1 =>
    let prev := greedyIdx p I t
    if h : prev + 3 < D + 1 then
      if p ⟨prev + 3, h⟩ ∈ I then prev + 4 else prev + 3
    else prev + 3

private lemma greedyIdx_le (p : Fin (D + 1) → V) (I : Finset V) [DecidableEq V] (t : ℕ) :
    greedyIdx p I t ≤ 4 * t + 1 := by
  induction t with
  | zero =>
    rw [greedyIdx]
    split_ifs <;> omega
  | succ t ih =>
    rw [greedyIdx]
    split_ifs <;> omega

private lemma greedyIdx_step (p : Fin (D + 1) → V) (I : Finset V) [DecidableEq V] (t : ℕ) :
    greedyIdx p I t + 3 ≤ greedyIdx p I (t + 1) := by
  rw [greedyIdx]
  split_ifs <;> omega

private lemma greedyIdx_gap (p : Fin (D + 1) → V) (I : Finset V) [DecidableEq V]
    {a b : ℕ} (hab : a < b) :
    greedyIdx p I a + 3 ≤ greedyIdx p I b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction k with
  | zero => exact greedyIdx_step p I a
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := greedyIdx_step p I (a + k + 1)
    have h3 : a + (k + 1) + 1 = a + k + 1 + 1 := by omega
    rw [h3]
    omega

private lemma greedyIdx_not_mem (G : SimpleGraph V) [DecidableEq V]
    {D : ℕ} (p : Fin (D + 1) → V)
    (hp_adj : ∀ i : Fin D, G.Adj (p i.castSucc) (p i.succ))
    {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    {t : ℕ} (ht : 4 * t + 1 ≤ D) :
    ∃ hlt : greedyIdx p I t < D + 1, p ⟨greedyIdx p I t, hlt⟩ ∉ I := by
  have hle : greedyIdx p I t ≤ 4 * t + 1 := greedyIdx_le p I t
  have hlt : greedyIdx p I t < D + 1 := by omega
  refine ⟨hlt, ?_⟩
  cases t with
  | zero =>
    have hD : 0 < D := by omega
    have h0 : 0 < D + 1 := Nat.zero_lt_succ D
    simp only [greedyIdx, h0, ↓reduceDIte]
    split_ifs with hmem
    · intro hmem1
      have hadj : G.Adj (p ⟨0, h0⟩) (p ⟨1, by omega⟩) := hp_adj ⟨0, hD⟩
      exact hI (mem_coe.mpr hmem) (mem_coe.mpr hmem1) hadj.ne hadj
    · exact hmem
  | succ t =>
    have hprev_le : greedyIdx p I t ≤ 4 * t + 1 := greedyIdx_le p I t
    have h3lt : greedyIdx p I t + 3 < D + 1 := by omega
    have h3ltD : greedyIdx p I t + 3 < D := by omega
    simp only [greedyIdx, h3lt, ↓reduceDIte]
    split_ifs with hmem
    · intro hmem4
      have hadj : G.Adj (p ⟨greedyIdx p I t + 3, h3lt⟩) (p ⟨greedyIdx p I t + 4, by omega⟩) :=
        hp_adj ⟨greedyIdx p I t + 3, h3ltD⟩
      exact hI (mem_coe.mpr hmem) (mem_coe.mpr hmem4) hadj.ne hadj
    · exact hmem

/--
**Greedy Diametral 3-Packing Bound (Lemma 2 — unconditional):**
For every finite simple connected graph `G`,
`G.indepNum + (G.diam + 3) / 4 ≤ G.largestInducedForestSize`.
Note `(D + 3) / 4 = ⌈D / 4⌉` for all `D : ℕ`.
-/
theorem indepNum_add_ceil_diam_div_four_le_largestInducedForestSize
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hconn : G.Connected) :
    G.indepNum + (G.diam + 3) / 4 ≤ G.largestInducedForestSize := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨p, hp_adj, _, hp_edist⟩ := exists_diametral_geodesic G hconn
  set r := (G.diam + 3) / 4
  have hr_bound : ∀ t : Fin r, 4 * t.val + 1 ≤ G.diam := by
    intro t
    have : t.val < (G.diam + 3) / 4 := t.isLt
    omega
  have hlt_all : ∀ t : Fin r, greedyIdx p I t.val < G.diam + 1 := fun t =>
    (greedyIdx_not_mem G p hp_adj hI.isIndepSet (hr_bound t)).1
  let f : Fin r → V := fun t => p ⟨greedyIdx p I t.val, hlt_all t⟩
  have hf_edist : ∀ a b : Fin r, a ≠ b → (3 : ℕ∞) ≤ G.edist (f a) (f b) := by
    intro a b hab
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · have hgap := greedyIdx_gap p I hlt
      have hle : (⟨greedyIdx p I a.val, hlt_all a⟩ : Fin (G.diam + 1)).val ≤
          (⟨greedyIdx p I b.val, hlt_all b⟩ : Fin (G.diam + 1)).val := by
        dsimp only; omega
      rw [hp_edist _ _ hle]
      dsimp only
      exact_mod_cast (by omega : 3 ≤ greedyIdx p I b.val - greedyIdx p I a.val)
    · have hgap := greedyIdx_gap p I hgt
      have hle : (⟨greedyIdx p I b.val, hlt_all b⟩ : Fin (G.diam + 1)).val ≤
          (⟨greedyIdx p I a.val, hlt_all a⟩ : Fin (G.diam + 1)).val := by
        dsimp only; omega
      rw [SimpleGraph.edist_comm, hp_edist _ _ hle]
      dsimp only
      exact_mod_cast (by omega : 3 ≤ greedyIdx p I a.val - greedyIdx p I b.val)
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h3 := hf_edist a b hne
    rw [hab, SimpleGraph.edist_self] at h3
    exact absurd h3 (by decide)
  let W : Finset V := Finset.univ.image f
  have hW_card : W.card = r := by
    rw [card_image_of_injective _ hf_inj, card_fin]
  have hW_pack : IsThreePacking G W := by
    intro u hu w hw huw
    rcases mem_image.mp hu with ⟨a, _, rfl⟩
    rcases mem_image.mp hw with ⟨b, _, rfl⟩
    have hab : a ≠ b := fun h => huw (congrArg f h)
    exact hf_edist a b hab
  have hdisj : Disjoint I W := by
    rw [Finset.disjoint_right]
    intro u hu
    rcases mem_image.mp hu with ⟨t, _, rfl⟩
    exact (greedyIdx_not_mem G p hp_adj hI.isIndepSet (hr_bound t)).2
  have hbound := card_indep_add_threePacking_le_largestInducedForestSize G hI.isIndepSet hW_pack hdisj
  rwa [hI.card_eq, hW_card] at hbound

/-- Small-diameter arithmetic identity: `⌈D / 4⌉ = ⌈D / 3⌉` for `D ∈ {0, 1, 2, 3, 5, 6, 9}`. -/
theorem ceil_div_four_eq_ceil_div_three_of_small_diam {D : ℕ}
    (hD : D = 0 ∨ D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 5 ∨ D = 6 ∨ D = 9) :
    (D + 3) / 4 = (D + 2) / 3 := by
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Corollary 4 (unconditional `α`-form):**
For `G.diam ∈ {0, 1, 2, 3, 5, 6, 9}`, `G.indepNum + (G.diam + 2) / 3 ≤ f(G)`. -/
theorem indepNum_add_ceil_diam_div_three_le_of_small_diam
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hD : G.diam = 0 ∨ G.diam = 1 ∨ G.diam = 2 ∨ G.diam = 3 ∨
      G.diam = 5 ∨ G.diam = 6 ∨ G.diam = 9) :
    G.indepNum + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  rw [← ceil_div_four_eq_ceil_div_three_of_small_diam hD]
  exact indepNum_add_ceil_diam_div_four_le_largestInducedForestSize G hconn

/--
**Corollary 4 (CONDITIONAL BOUNDARY on explicit FMS premise `residue G ≤ G.indepNum`):**
For every finite connected graph `G` with `G.diam ∈ {0, 1, 2, 3, 5, 6, 9}`,
assuming `hFMS : residue G ≤ G.indepNum`, WOWII #61 holds:
`residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`.
-/
theorem wowii61_of_small_diam_conditional
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hD : G.diam = 0 ∨ G.diam = 1 ∨ G.diam = 2 ∨ G.diam = 3 ∨
      G.diam = 5 ∨ G.diam = 6 ∨ G.diam = 9)
    (hFMS : SimpleGraph.residue G ≤ G.indepNum) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  have h := indepNum_add_ceil_diam_div_three_le_of_small_diam G hconn hD
  omega

/-! ## 4. Monotone 3-Packings & Induced-Matching Residue (IMR) Reduction (Theorem 5) -/

/-- An *induced matching* of size `k` in `G` with explicit bipartition `(A, B)`:
disjoint independent sets `A, B` of size `k` enumerated by `a, b : Fin k → V`
such that the only edges between `A` and `B` are `a i ~ b i`. -/
structure InducedMatching [DecidableEq V] (G : SimpleGraph V) (k : ℕ) where
  a : Fin k → V
  b : Fin k → V
  A : Finset V
  B : Finset V
  A_eq : A = Finset.univ.image a
  B_eq : B = Finset.univ.image b
  A_card : A.card = k
  B_card : B.card = k
  disjoint_AB : Disjoint A B
  A_indep : G.IsIndepSet (A : Set V)
  B_indep : G.IsIndepSet (B : Set V)
  adj_iff : ∀ i j : Fin k, G.Adj (a i) (b j) ↔ i = j

/--
**Monotone 3-Packing Family & Diametral Induced Matching (Theorem 5 — unconditional):**
For every nontrivial finite connected graph `G` with `k = (G.diam + 2) / 3`:
1. There is a family `W : Fin (k + 1) → Finset V` of `k + 1` monotone 3-packings of size `k`
   along a diametral geodesic, each giving `α(G - W r) + k ≤ f(G)`.
2. The extreme pair `(W k, W 0)` forms an induced matching `M` of size `k`, giving
   `max (α(G - M.A)) (α(G - M.B)) + k ≤ f(G)`.
-/
theorem exists_diametral_monotone_threePackings_and_inducedMatching
    [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hconn : G.Connected) :
    let k := (G.diam + 2) / 3
    ∃ (W : Fin (k + 1) → Finset V) (M : InducedMatching G k),
      M.A = W ⟨k, Nat.lt_succ_self k⟩ ∧
      M.B = W ⟨0, Nat.zero_lt_succ k⟩ ∧
      (∀ r : Fin (k + 1), IsThreePacking G (W r) ∧ (W r).card = k ∧
        (G.induce { u : V | u ∉ W r }).indepNum + k ≤ G.largestInducedForestSize) := by
  have : Nonempty V := inferInstance
  have hdiam_pos : 1 ≤ G.diam := by
    have hne_top : G.ediam ≠ ⊤ := by
      obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
      rw [← huv, SimpleGraph.edist_ne_top_iff_reachable]
      exact hconn u v
    obtain ⟨u, v, huv⟩ := exists_pair_ne V
    have h1 : (1 : ℕ∞) ≤ G.edist u v :=
      Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
    have hle : G.edist u v ≤ G.ediam := SimpleGraph.edist_le_ediam
    have h1' : (1 : ℕ∞) ≤ G.ediam := h1.trans hle
    have hcoe : (G.diam : ℕ∞) = G.ediam := ENat.natCast_toNat hne_top
    rw [← hcoe] at h1'
    exact_mod_cast h1'
  obtain ⟨p, hp_adj, hp_dist, hp_edist⟩ := exists_diametral_geodesic G hconn
  set k := (G.diam + 2) / 3
  have hk_bound : ∀ i : Fin k, 3 * i.val + 1 ≤ G.diam := by
    intro i
    have hi : i.val < (G.diam + 2) / 3 := i.isLt
    omega
  let pos (r : Fin (k + 1)) (i : Fin k) : Fin (G.diam + 1) :=
    ⟨if i.val < r.val then 3 * i.val else 3 * i.val + 1, by
      have := hk_bound i
      split_ifs <;> omega⟩
  have hpos_gap : ∀ (r : Fin (k + 1)) (i j : Fin k), i.val < j.val →
      (pos r i).val + 3 ≤ (pos r j).val := by
    intro r i j hij
    dsimp only [pos]
    split_ifs <;> omega
  let f (r : Fin (k + 1)) (i : Fin k) : V := p (pos r i)
  have hf_edist : ∀ (r : Fin (k + 1)) (i j : Fin k), i ≠ j →
      (3 : ℕ∞) ≤ G.edist (f r i) (f r j) := by
    intro r i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · have hgap := hpos_gap r i j hlt
      rw [hp_edist (pos r i) (pos r j) (by omega)]
      exact_mod_cast (by omega : 3 ≤ (pos r j).val - (pos r i).val)
    · have hgap := hpos_gap r j i hgt
      rw [SimpleGraph.edist_comm, hp_edist (pos r j) (pos r i) (by omega)]
      exact_mod_cast (by omega : 3 ≤ (pos r i).val - (pos r j).val)
  have hf_inj : ∀ r : Fin (k + 1), Function.Injective (f r) := by
    intro r i j hij
    by_contra hne
    have h3 := hf_edist r i j hne
    rw [hij, SimpleGraph.edist_self] at h3
    exact absurd h3 (by decide)
  let W : Fin (k + 1) → Finset V := fun r => Finset.univ.image (f r)
  have hW_pack : ∀ r : Fin (k + 1), IsThreePacking G (W r) := by
    intro r u hu w hw huw
    rcases mem_image.mp hu with ⟨i, _, rfl⟩
    rcases mem_image.mp hw with ⟨j, _, rfl⟩
    exact hf_edist r i j (fun h => huw (congrArg (f r) h))
  have hW_card : ∀ r : Fin (k + 1), (W r).card = k := by
    intro r
    rw [card_image_of_injective _ (hf_inj r), card_fin]
  let rk : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let r0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
  have hpos_rk : ∀ i : Fin k, (pos rk i).val = 3 * i.val := by
    intro i; simp [pos, rk, i.isLt]
  have hpos_r0 : ∀ i : Fin k, (pos r0 i).val = 3 * i.val + 1 := by
    intro i; simp [pos, r0]
  have hdisj_AB : Disjoint (W rk) (W r0) := by
    rw [Finset.disjoint_left]
    intro u huA huB
    rcases mem_image.mp huA with ⟨i, _, rfl⟩
    rcases mem_image.mp huB with ⟨j, _, hj⟩
    have hdist0 : G.dist (p (pos rk i)) (p (pos r0 j)) = 0 := by
      change G.dist (f rk i) (f r0 j) = 0
      rw [hj, SimpleGraph.dist_self]
    have hi := hpos_rk i
    have hj' := hpos_r0 j
    rcases le_total (pos rk i).val (pos r0 j).val with hle | hle
    · have h := hp_dist (pos rk i) (pos r0 j) hle
      omega
    · have h := hp_dist (pos r0 j) (pos rk i) hle
      rw [SimpleGraph.dist_comm] at hdist0
      omega
  have hadj_AB : ∀ i j : Fin k, G.Adj (f rk i) (f r0 j) ↔ i = j := by
    intro i j
    constructor
    · intro hadj
      have hdist1 : G.dist (p (pos rk i)) (p (pos r0 j)) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have hi := hpos_rk i
      have hj' := hpos_r0 j
      rcases le_total (pos rk i).val (pos r0 j).val with hle | hle
      · have h := hp_dist (pos rk i) (pos r0 j) hle
        exact Fin.ext (by omega)
      · have h := hp_dist (pos r0 j) (pos rk i) hle
        rw [SimpleGraph.dist_comm] at hdist1
        exact Fin.ext (by omega)
    · rintro rfl
      have hidx : 3 * i.val < G.diam := by have := hk_bound i; omega
      have h1 : pos rk i = (⟨3 * i.val, hidx⟩ : Fin G.diam).castSucc := by
        apply Fin.ext; simpa using hpos_rk i
      have h2 : pos r0 i = (⟨3 * i.val, hidx⟩ : Fin G.diam).succ := by
        apply Fin.ext; simpa using hpos_r0 i
      change G.Adj (p (pos rk i)) (p (pos r0 i))
      rw [h1, h2]
      exact hp_adj ⟨3 * i.val, hidx⟩
  let M : InducedMatching G k :=
    { a := f rk
      b := f r0
      A := W rk
      B := W r0
      A_eq := rfl
      B_eq := rfl
      A_card := hW_card rk
      B_card := hW_card r0
      disjoint_AB := hdisj_AB
      A_indep := (hW_pack rk).isIndepSet
      B_indep := (hW_pack r0).isIndepSet
      adj_iff := hadj_AB }
  refine ⟨W, M, rfl, rfl, fun r => ⟨hW_pack r, hW_card r, ?_⟩⟩
  rw [← hW_card r]
  exact indepNum_compl_add_card_le_largestInducedForestSize G (W r) (hW_pack r)

/-- **Unconditional IMR Reduction Theorem (Theorem 5):**
If the Induced-Matching Residue (IMR) inequality holds for the diametral induced matching of `G`
(in particular, if it holds for all induced matchings of `G`), then WOWII Conjecture 61 holds
for `G` in exact integer form: `residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`. -/
theorem wowii61_of_imr_premise
    [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hIMR : ∀ M : InducedMatching G ((G.diam + 2) / 3),
      SimpleGraph.residue G ≤
        max (G.induce { u : V | u ∉ M.A }).indepNum
            (G.induce { u : V | u ∉ M.B }).indepNum) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  obtain ⟨W, M, hA, hB, hW⟩ :=
    exists_diametral_monotone_threePackings_and_inducedMatching G hconn
  have h1 := hIMR M
  rcases le_max_iff.mp h1 with hleA | hleB
  · have hbound := (hW ⟨(G.diam + 2) / 3, Nat.lt_succ_self _⟩).2.2
    rw [← hA] at hbound
    omega
  · have hbound := (hW ⟨0, Nat.zero_lt_succ _⟩).2.2
    rw [← hB] at hbound
    omega

/-- **Unconditional Monotone-IMR Reduction Theorem:**
Even the strictly weaker *Monotone IMR* premise — that at least one of the `k + 1`
monotone 3-packings `W r` along a diametral geodesic satisfies `residue G ≤ α(G - W r)` —
already implies WOWII Conjecture 61 (`residue G + (G.diam + 2) / 3 ≤ f(G)`). -/
theorem wowii61_of_monotone_imr_premise
    [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hMono : ∀ W : Fin ((G.diam + 2) / 3 + 1) → Finset V,
      (∀ r, IsThreePacking G (W r) ∧ (W r).card = (G.diam + 2) / 3) →
      ∃ r, SimpleGraph.residue G ≤ (G.induce { u : V | u ∉ W r }).indepNum) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  obtain ⟨W, _, _, _, hW⟩ :=
    exists_diametral_monotone_threePackings_and_inducedMatching G hconn
  obtain ⟨r, hr⟩ := hMono W (fun r => ⟨(hW r).1, (hW r).2.1⟩)
  have hbound := (hW r).2.2
  omega

/-! ## 5. Exact `D = 4` Tight-Boundary Anatomy (Theorem 7) -/

private lemma adj_both_of_distinct_in_pair {G : SimpleGraph V} {a b x y z : V}
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : G.Adj a z ∧ G.Adj b z := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨hxz, hyz⟩
  · exact ⟨hyz, hxz⟩
  · exact absurd rfl hxy

private lemma third_eq_first_of_pair {a b x y z : V}
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (hz : z = a ∨ z = b)
    (hxy : x ≠ y) (hyz : y ≠ z) : z = x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    first | rfl | exact absurd rfl hxy | exact absurd rfl hyz

private lemma isAcyclic_induce_union_pair_of_at_most_one_common [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} {a b : V}
    (hI : G.IsIndepSet (I : Set V)) (hnab : ¬ G.Adj a b)
    (hcommon : ∀ x ∈ I, ∀ y ∈ I, G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y) :
    (G.induce ((insert a (insert b I) : Finset V) : Set V)).IsAcyclic := by
  intro u c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hnodup_e : c.edges.Nodup := hc.edges_nodup
  have hnodup_s : c.support.tail.Nodup := hc.support_nodup
  have mem_ab_of_not_I : ∀ x : { z : V // z ∈ (insert a (insert b I) : Finset V) },
      x.1 ∉ I → x.1 = a ∨ x.1 = b := by
    intro x hx
    rcases mem_insert.mp (mem_coe.mp x.2) with h | h
    · exact Or.inl h
    · exact Or.inr ((mem_insert.mp h).resolve_right hx)
  have pair_adj_imp : ∀ x y : { z : V // z ∈ (insert a (insert b I) : Finset V) },
      G.Adj x.1 y.1 → (x.1 ∈ I ↔ y.1 ∉ I) := by
    intro x y hxy
    constructor
    · intro hx hy
      exact hI (mem_coe.mpr hx) (mem_coe.mpr hy) hxy.ne hxy
    · intro hy_not
      by_contra hx_not
      have hx_ab := mem_ab_of_not_I x hx_not
      have hy_ab := mem_ab_of_not_I y hy_not
      rcases hx_ab with hx' | hx' <;> rcases hy_ab with hy' | hy'
      · exact hxy.ne (hx'.trans hy'.symm)
      · rw [hx', hy'] at hxy; exact hnab hxy
      · rw [hx', hy'] at hxy; exact hnab hxy.symm
      · exact hxy.ne (hx'.trans hy'.symm)
  match c with
  | .nil => simp at hlen
  | .cons _ .nil => simp at hlen
  | .cons _ (.cons _ .nil) => simp at hlen
  | .cons (u := v₀) (v := v₁) h01 (.cons (v := v₂) h12 (.cons (v := v₃) h23 rest)) =>
    have h01' : G.Adj v₀.1 v₁.1 := h01
    have h12' : G.Adj v₁.1 v₂.1 := h12
    have h23' : G.Adj v₂.1 v₃.1 := h23
    cases rest with
    | nil =>
      have h1 := pair_adj_imp v₀ v₁ h01'
      have h2 := pair_adj_imp v₁ v₂ h12'
      have h3 := pair_adj_imp v₂ v₀ h23'
      tauto
    | @cons _ v₄ _ h34 rest' =>
      have h34' : G.Adj v₃.1 v₄.1 := h34
      simp only [Walk.edges_cons, List.nodup_cons, List.mem_cons, not_or] at hnodup_e
      simp only [Walk.support_cons, List.tail_cons, List.nodup_cons, List.mem_cons,
        not_or] at hnodup_s
      have hv0_ne_v2 : v₀.1 ≠ v₂.1 := by
        intro h; exact hnodup_e.1.1 (by rw [Subtype.ext h]; exact Sym2.eq_swap)
      have hv1_ne_v3 : v₁.1 ≠ v₃.1 := fun h => hnodup_s.1.2.1 (Subtype.ext h)
      have hv2_ne_v4 : v₂.1 ≠ v₄.1 := by
        intro h; exact hnodup_e.2.2.1.1 (by rw [Subtype.ext h]; exact Sym2.eq_swap)
      by_cases hv0I : v₀.1 ∈ I
      · have hv1_notI : v₁.1 ∉ I := (pair_adj_imp v₀ v₁ h01').mp hv0I
        have hv2I : v₂.1 ∈ I := (pair_adj_imp v₂ v₁ h12'.symm).mpr hv1_notI
        have hv3_notI : v₃.1 ∉ I := (pair_adj_imp v₂ v₃ h23').mp hv2I
        have hv4I : v₄.1 ∈ I := (pair_adj_imp v₄ v₃ h34'.symm).mpr hv3_notI
        have hv1_ab := mem_ab_of_not_I v₁ hv1_notI
        have hv3_ab := mem_ab_of_not_I v₃ hv3_notI
        have ⟨hv2_a, hv2_b⟩ := adj_both_of_distinct_in_pair hv1_ab hv3_ab hv1_ne_v3 h12' h23'.symm
        cases rest' with
        | nil =>
          have ⟨hv0_a, hv0_b⟩ := adj_both_of_distinct_in_pair hv1_ab hv3_ab hv1_ne_v3 h01'.symm h34'
          exact hv0_ne_v2 (hcommon v₀.1 hv0I v₂.1 hv2I hv0_a hv0_b hv2_a hv2_b)
        | @cons _ v₅ _ h45 rest'' =>
          have h45' : G.Adj v₄.1 v₅.1 := h45
          have hv5_notI : v₅.1 ∉ I := (pair_adj_imp v₄ v₅ h45').mp hv4I
          have hv5_ab := mem_ab_of_not_I v₅ hv5_notI
          have hv3_ne_v5 : v₃.1 ≠ v₅.1 := by
            simp only [Walk.edges_cons, List.mem_cons, not_or] at hnodup_e
            intro h
            exact hnodup_e.2.2.2.1.1 (by rw [Subtype.ext h]; exact Sym2.eq_swap)
          have hv5_eq_v1 : v₅ = v₁ :=
            Subtype.ext (third_eq_first_of_pair hv1_ab hv3_ab hv5_ab hv1_ne_v3 hv3_ne_v5)
          simp only [Walk.support_cons, List.mem_cons, not_or] at hnodup_s
          exact hnodup_s.1.2.2.2 (hv5_eq_v1 ▸ rest''.start_mem_support)
      · have hv1I : v₁.1 ∈ I := (pair_adj_imp v₁ v₀ h01'.symm).mpr hv0I
        have hv2_notI : v₂.1 ∉ I := (pair_adj_imp v₁ v₂ h12').mp hv1I
        have hv3I : v₃.1 ∈ I := (pair_adj_imp v₃ v₂ h23'.symm).mpr hv2_notI
        have hv4_notI : v₄.1 ∉ I := (pair_adj_imp v₃ v₄ h34').mp hv3I
        have hv0_ab := mem_ab_of_not_I v₀ hv0I
        have hv2_ab := mem_ab_of_not_I v₂ hv2_notI
        have hv4_ab := mem_ab_of_not_I v₄ hv4_notI
        have hv4_eq_v0 : v₄.1 = v₀.1 :=
          third_eq_first_of_pair hv0_ab hv2_ab hv4_ab hv0_ne_v2 hv2_ne_v4
        have ⟨hv1_a, hv1_b⟩ := adj_both_of_distinct_in_pair hv0_ab hv2_ab hv0_ne_v2 h01' h12'.symm
        have h03 : G.Adj v₀.1 v₃.1 := by rw [← hv4_eq_v0]; exact h34'.symm
        have ⟨hv3_a, hv3_b⟩ := adj_both_of_distinct_in_pair hv0_ab hv2_ab hv0_ne_v2 h03 h23'
        exact hv1_ne_v3 (hcommon v₁.1 hv1I v₃.1 hv3I hv1_a hv1_b hv3_a hv3_b)

/--
**Exact `D = 4` Tight-Boundary Anatomy (Theorem 7 — unconditional):**
If `G` is finite and connected with `f(G) ≤ α(G) + 1`, `I` is a maximum independent set
of `G`, and `u, w` satisfy `G.dist u w = 4`, then:
1. `u ∈ I` and `w ∈ I`,
2. `N(u)` and `N(w)` are disjoint subsets of `V \ I` with no edges between them,
3. every `a ∈ N(u)` and `b ∈ N(w)` share at least 2 common neighbors in `I`.
-/
theorem diam_four_tight_anatomy [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (htight : G.largestInducedForestSize ≤ G.indepNum + 1)
    {I : Finset V} (hI : G.IsNIndepSet G.indepNum I)
    {u w : V} (hd : G.dist u w = 4) :
    u ∈ I ∧ w ∈ I ∧
    Disjoint (G.neighborFinset u) (G.neighborFinset w) ∧
    (∀ a ∈ G.neighborFinset u, ∀ b ∈ G.neighborFinset w, ¬ G.Adj a b) ∧
    (∀ a ∈ G.neighborFinset u, ∀ b ∈ G.neighborFinset w,
      2 ≤ ((G.neighborFinset a ∩ G.neighborFinset b) ∩ I).card) := by
  have hed : G.edist u w = (4 : ℕ∞) := by
    rw [← (hconn u w).coe_dist_eq_edist, hd]
    rfl
  have huw_ne : u ≠ w := by
    intro h; subst h; simp at hd
  obtain ⟨p, _, hp_len⟩ := hconn.exists_path_of_dist u w
  have hp4 : p.length = 4 := hp_len.trans hd
  have hp_end : p.getVert 4 = w := by
    rw [← hp4, Walk.getVert_length]
  have huI : u ∈ I := by
    by_contra hu_not
    set v₃ := p.getVert 3
    have hv₃_adj_w : G.Adj v₃ w := by
      have h := p.adj_getVert_succ (i := 3) (by omega)
      simpa [v₃, hp_end] using h
    have hd_u_v3 : G.dist u v₃ = 3 := by
      have hle1 : G.dist u v₃ ≤ 3 := by
        simpa [v₃, Walk.getVert_zero] using
          dist_getVert_le_sub hconn p (i := 0) (j := 3) (by omega) (by omega)
      have htri : G.dist u w ≤ G.dist u v₃ + G.dist v₃ w :=
        (hconn u v₃).dist_triangle_left w
      have h1 : G.dist v₃ w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hv₃_adj_w
      omega
    have hed_u_v3 : (3 : ℕ∞) ≤ G.edist u v₃ := by
      rw [← (hconn u v₃).coe_dist_eq_edist, hd_u_v3]
      exact le_rfl
    have hpair : ∃ z, z ∉ I ∧ u ≠ z ∧ (3 : ℕ∞) ≤ G.edist u z := by
      by_cases hv3I : v₃ ∈ I
      · have hw_not : w ∉ I := fun hwI =>
          hI.isIndepSet (mem_coe.mpr hv3I) (mem_coe.mpr hwI) hv₃_adj_w.ne hv₃_adj_w
        exact ⟨w, hw_not, huw_ne, by rw [hed]; decide⟩
      · have huv3 : u ≠ v₃ := by intro h; rw [h, SimpleGraph.dist_self] at hd_u_v3; omega
        exact ⟨v₃, hv3I, huv3, hed_u_v3⟩
    rcases hpair with ⟨z, hz_not, huz, h3⟩
    let W : Finset V := {u, z}
    have hW_pack : IsThreePacking G W := by
      intro x hx y hy hxy
      simp only [W, mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact h3
      · exact SimpleGraph.edist_comm ▸ h3
      · exact absurd rfl hxy
    have hdisj : Disjoint I W := by
      rw [Finset.disjoint_right]
      intro x hx
      simp only [W, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hW_card : W.card = 2 := card_pair huz
    have hbound :=
      card_indep_add_threePacking_le_largestInducedForestSize G hI.isIndepSet hW_pack hdisj
    rw [hI.card_eq, hW_card] at hbound
    omega
  have hwI : w ∈ I := by
    by_contra hw_not
    set v₁ := p.getVert 1
    have hu_adj_v1 : G.Adj u v₁ := by
      have h := p.adj_getVert_succ (i := 0) (by omega)
      simpa [v₁, Walk.getVert_zero] using h
    have hd_v1_w : G.dist v₁ w = 3 := by
      have hle1 : G.dist v₁ w ≤ 3 := by
        have h := dist_getVert_le_sub hconn p (i := 1) (j := 4) (by omega) (by omega)
        simpa [v₁, hp_end] using h
      have htri : G.dist u w ≤ G.dist u v₁ + G.dist v₁ w :=
        (hconn u v₁).dist_triangle_left w
      have h1 : G.dist u v₁ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj_v1
      omega
    have hed_w_v1 : (3 : ℕ∞) ≤ G.edist w v₁ := by
      rw [SimpleGraph.edist_comm, ← (hconn v₁ w).coe_dist_eq_edist, hd_v1_w]
      exact le_rfl
    have hv1_not : v₁ ∉ I := fun hv1I =>
      hI.isIndepSet (mem_coe.mpr huI) (mem_coe.mpr hv1I) hu_adj_v1.ne hu_adj_v1
    have hwv1 : w ≠ v₁ := by intro h; rw [← h, SimpleGraph.dist_self] at hd_v1_w; omega
    let W : Finset V := {w, v₁}
    have hW_pack : IsThreePacking G W := by
      intro x hx y hy hxy
      simp only [W, mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hed_w_v1
      · exact SimpleGraph.edist_comm ▸ hed_w_v1
      · exact absurd rfl hxy
    have hdisj : Disjoint I W := by
      rw [Finset.disjoint_right]
      intro x hx
      simp only [W, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hW_card : W.card = 2 := card_pair hwv1
    have hbound :=
      card_indep_add_threePacking_le_largestInducedForestSize G hI.isIndepSet hW_pack hdisj
    rw [hI.card_eq, hW_card] at hbound
    omega
  have hdisj_N : Disjoint (G.neighborFinset u) (G.neighborFinset w) := by
    rw [Finset.disjoint_left]
    intro a hau haw
    rw [SimpleGraph.mem_neighborFinset] at hau haw
    have htri : G.dist u w ≤ G.dist u a + G.dist a w := (hconn u a).dist_triangle_left w
    have h1 : G.dist u a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hau
    have h2 : G.dist a w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haw.symm
    omega
  have hno_edge : ∀ a ∈ G.neighborFinset u, ∀ b ∈ G.neighborFinset w, ¬ G.Adj a b := by
    intro a hau b hbw hab
    rw [SimpleGraph.mem_neighborFinset] at hau hbw
    have htri1 : G.dist u w ≤ G.dist u a + G.dist a w := (hconn u a).dist_triangle_left w
    have htri2 : G.dist a w ≤ G.dist a b + G.dist b w := (hconn a b).dist_triangle_left w
    have h1 : G.dist u a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hau
    have h2 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
    have h3 : G.dist b w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbw.symm
    omega
  refine ⟨huI, hwI, hdisj_N, hno_edge, ?_⟩
  intro a hau b hbw
  by_contra hlt
  have hle1 : ((G.neighborFinset a ∩ G.neighborFinset b) ∩ I).card ≤ 1 := by omega
  have hcommon : ∀ x ∈ I, ∀ y ∈ I, G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y := by
    intro x hx y hy hax hbx hay hby
    have hx' : x ∈ (G.neighborFinset a ∩ G.neighborFinset b) ∩ I := by
      simp [mem_inter, SimpleGraph.mem_neighborFinset, hax, hbx, hx]
    have hy' : y ∈ (G.neighborFinset a ∩ G.neighborFinset b) ∩ I := by
      simp [mem_inter, SimpleGraph.mem_neighborFinset, hay, hby, hy]
    exact Finset.card_le_one.mp hle1 x hx' y hy'
  have hau' : G.Adj u a := (G.mem_neighborFinset u a).mp hau
  have hbw' : G.Adj w b := (G.mem_neighborFinset w b).mp hbw
  have haI : a ∉ I := fun ha => hI.isIndepSet (mem_coe.mpr huI) (mem_coe.mpr ha) hau'.ne hau'
  have hbI : b ∉ I := fun hb => hI.isIndepSet (mem_coe.mpr hwI) (mem_coe.mpr hb) hbw'.ne hbw'
  have hab : a ≠ b := fun h => (Finset.disjoint_left.mp hdisj_N) hau (h ▸ hbw)
  have hnab : ¬ G.Adj a b := hno_edge a hau b hbw
  have hacyc :=
    isAcyclic_induce_union_pair_of_at_most_one_common G hI.isIndepSet hnab hcommon
  have hcard_le := card_le_largestInducedForestSize G hacyc
  have ha_not : a ∉ insert b I := by simp [hab, haI]
  rw [card_insert_of_notMem ha_not, card_insert_of_notMem hbI, hI.card_eq] at hcard_le
  omega

end WOWII61.PackingForest
