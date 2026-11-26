module

public import WOWII61.Defs

/-!
# Havel–Hakimi Sequence Definitions & Structural Lemmas (`WOWII61.ResidueSeq`)

Purely arithmetic definitions (`IsHHValid`, `ExchangeStep`, `DominatedBy`, `SafeDoubleDec`,
`phiStep`) and elementary sorted-list / multiset / `havelHakimiStep` / `residueAux` lemmas
for the exact staged `SimpleGraph.havelHakimiStep` and `SimpleGraph.residueAux` from
`StagedDeps.Residue`.

Zero `SimpleGraph` construction machinery is used here.
-/

@[expose] public section

namespace WOWII61.ResidueSeq

open SimpleGraph

/-! ## 1. Core Purely Arithmetic Definitions -/

/-- Purely arithmetic Havel–Hakimi validity (no underflow at any HH step).
On descending sorted lists (`s.Pairwise (· ≥ ·)`), this is equivalent to graphicality. -/
def IsHHValid : List ℕ → Prop
  | [] => True
  | d :: rest =>
    d ≤ rest.length ∧
    (∀ x ∈ rest.take d, 1 ≤ x) ∧
    IsHHValid (SimpleGraph.havelHakimiStep (d :: rest))
termination_by l => l.length
decreasing_by
  simp [SimpleGraph.havelHakimiStep_length_cons]

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

/-- Safe double-decrement relation from descending sorted list `b = d :: rb` (`1 ≤ d ≤ rb.length`)
to descending sorted list `a`: decrementing either two distinct entries `x ≥ y ≥ 1` with
`y ≤ b_{d+1} + 1` (0-indexed `rb.getD (d - 1) 0 + 1`), or one entry `x ≥ 2` twice with
`x ≤ b_{d+1} + 1`. -/
def SafeDoubleDec (b a : List ℕ) : Prop :=
  b.Pairwise (· ≥ ·) ∧ a.Pairwise (· ≥ ·) ∧
  ∃ (d : ℕ) (rb : List ℕ),
    b = d :: rb ∧ 1 ≤ d ∧ d ≤ rb.length ∧
    ((∃ (m : Multiset ℕ) (x y : ℕ),
        1 ≤ y ∧ y ≤ x ∧ y ≤ rb.getD (d - 1) 0 + 1 ∧
        (b : Multiset ℕ) = x ::ₘ y ::ₘ m ∧
        (a : Multiset ℕ) = (x - 1) ::ₘ (y - 1) ::ₘ m) ∨
     (∃ (m : Multiset ℕ) (x : ℕ),
        2 ≤ x ∧ x ≤ rb.getD (d - 1) 0 + 1 ∧
        (b : Multiset ℕ) = x ::ₘ m ∧
        (a : Multiset ℕ) = (x - 2) ::ₘ m))

/-- The decrement-top-`d`-and-sort-descending operator `Φ_d(r)` on a list `r`. -/
def phiStep (d : ℕ) (r : List ℕ) : List ℕ :=
  ((r.take d).map (· - 1) ++ r.drop d).mergeSort (· ≥ ·)

/-! ## 2. Basic Equational Lemmas for `IsHHValid`, `havelHakimiStep`, `phiStep`, `residueAux` -/

@[simp]
theorem isHHValid_nil : IsHHValid [] ↔ True := by
  rw [IsHHValid]

@[simp]
theorem isHHValid_cons (d : ℕ) (rest : List ℕ) :
    IsHHValid (d :: rest) ↔
      d ≤ rest.length ∧
      (∀ x ∈ rest.take d, 1 ≤ x) ∧
      IsHHValid (SimpleGraph.havelHakimiStep (d :: rest)) := by
  conv_lhs => rw [IsHHValid]

theorem havelHakimiStep_cons_eq_phiStep (d : ℕ) (r : List ℕ) :
    SimpleGraph.havelHakimiStep (d :: r) = phiStep d r := by
  simp [SimpleGraph.havelHakimiStep, phiStep, List.splitAt_eq]

theorem isHHValid_havelHakimiStep {s : List ℕ} (h : IsHHValid s) :
    IsHHValid (SimpleGraph.havelHakimiStep s) := by
  cases s with
  | nil => simp [SimpleGraph.havelHakimiStep]
  | cons d rest => exact ((isHHValid_cons d rest).mp h).2.2

theorem pairwise_mergeSort_ge (l : List ℕ) : (l.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) := by
  simpa using (List.pairwise_mergeSort' (r := (· ≥ ·)) l)

theorem pairwise_phiStep (d : ℕ) (r : List ℕ) : (phiStep d r).Pairwise (· ≥ ·) :=
  pairwise_mergeSort_ge _

theorem pairwise_havelHakimiStep_cons (d : ℕ) (r : List ℕ) :
    (SimpleGraph.havelHakimiStep (d :: r)).Pairwise (· ≥ ·) := by
  rw [havelHakimiStep_cons_eq_phiStep]
  exact pairwise_phiStep d r

theorem coe_mergeSort_ge (l : List ℕ) :
    ((l.mergeSort (· ≥ ·) : List ℕ) : Multiset ℕ) = (l : Multiset ℕ) :=
  Quot.sound (List.mergeSort_perm l (· ≥ ·))

theorem coe_phiStep (d : ℕ) (r : List ℕ) :
    (phiStep d r : Multiset ℕ) = (((r.take d).map (· - 1) ++ r.drop d : List ℕ) : Multiset ℕ) :=
  coe_mergeSort_ge _

theorem length_phiStep (d : ℕ) (r : List ℕ) : (phiStep d r).length = r.length := by
  rw [← havelHakimiStep_cons_eq_phiStep, SimpleGraph.havelHakimiStep_length_cons]

theorem eq_of_coe_eq_of_pairwise {l₁ l₂ : List ℕ}
    (h₁ : l₁.Pairwise (· ≥ ·)) (h₂ : l₂.Pairwise (· ≥ ·))
    (hcoe : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) : l₁ = l₂ := by
  have hperm : l₁.Perm l₂ := Multiset.coe_eq_coe.mp hcoe
  exact hperm.eq_of_pairwise' h₁ h₂

theorem residueAux_nil : SimpleGraph.residueAux [] = 0 := by
  rw [SimpleGraph.residueAux]

theorem residueAux_cons_zero (rest : List ℕ) :
    SimpleGraph.residueAux (0 :: rest) = 1 + rest.length := by
  rw [SimpleGraph.residueAux]

theorem residueAux_cons_pos {d : ℕ} (hd : 1 ≤ d) (rest : List ℕ) :
    SimpleGraph.residueAux (d :: rest) =
      SimpleGraph.residueAux (SimpleGraph.havelHakimiStep (d :: rest)) := by
  cases d with
  | zero => omega
  | succ k =>
    conv_lhs => unfold SimpleGraph.residueAux
    rfl

theorem residueAux_le_length (l : List ℕ) : SimpleGraph.residueAux l ≤ l.length := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp [residueAux_nil]
    | cons d rest =>
      cases d with
      | zero =>
        rw [residueAux_cons_zero]
        simp only [List.length_cons] at hn
        omega
      | succ k =>
        rw [residueAux_cons_pos (by omega)]
        have hlen : (SimpleGraph.havelHakimiStep ((k + 1) :: rest)).length = rest.length :=
          SimpleGraph.havelHakimiStep_length_cons (k + 1) rest
        have hlt : (SimpleGraph.havelHakimiStep ((k + 1) :: rest)).length < n := by
          rw [hlen]; simp only [List.length_cons] at hn; omega
        have hle := ih _ hlt _ rfl
        simp only [List.length_cons] at hn
        omega

/-! ## 3. Descending Sorted Lists, Heads, Sums, and Counting Bounds -/

theorem getElem_ge_of_pairwise_ge {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[j] ≤ l[i] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp hl i j hi hj hlt

theorem le_head_of_pairwise_ge {d : ℕ} {r : List ℕ} (h : (d :: r).Pairwise (· ≥ ·))
    {x : ℕ} (hx : x ∈ r) : x ≤ d :=
  (List.pairwise_cons.mp h).1 x hx

theorem head_eq_of_coe_cons_of_max {l : List ℕ} {d : ℕ} {m : Multiset ℕ}
    (hl : l.Pairwise (· ≥ ·))
    (hcoe : (l : Multiset ℕ) = d ::ₘ m)
    (hmax : ∀ x ∈ m, x ≤ d) :
    ∃ r : List ℕ, l = d :: r ∧ r.Pairwise (· ≥ ·) ∧ (r : Multiset ℕ) = m := by
  let r := m.sort (· ≥ ·)
  have hr_pw : r.Pairwise (· ≥ ·) := Multiset.pairwise_sort m (· ≥ ·)
  have hr_coe : (r : Multiset ℕ) = m := Multiset.sort_eq m (· ≥ ·)
  have hdr_pw : (d :: r).Pairwise (· ≥ ·) := by
    rw [List.pairwise_cons]
    refine ⟨?_, hr_pw⟩
    intro x hx
    have hxm : x ∈ m := by rwa [← hr_coe, Multiset.mem_coe]
    exact hmax x hxm
  have hEq : l = d :: r := eq_of_coe_eq_of_pairwise hl hdr_pw (by
    rw [hcoe, ← hr_coe]; rfl)
  exact ⟨r, hEq, hr_pw, hr_coe⟩

theorem sum_eq_zero_of_forall_zero {l : List ℕ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a = 0 := h a (by simp)
    have ht : t.sum = 0 := ih (fun x hx => h x (by simp [hx]))
    simp [ha, ht]

theorem sum_eq_zero_of_head_zero {r : List ℕ} (h : (0 :: r).Pairwise (· ≥ ·)) :
    (0 :: r).sum = 0 := by
  have hall : ∀ x ∈ r, x = 0 := fun x hx => Nat.le_zero.mp (le_head_of_pairwise_ge h hx)
  simp [sum_eq_zero_of_forall_zero hall]

theorem exists_cons_pos_of_sum_pos {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) (hsum : 0 < l.sum) :
    ∃ d r, l = d :: r ∧ 1 ≤ d := by
  cases l with
  | nil => simp at hsum
  | cons d r =>
    cases d with
    | zero =>
      have h0 := sum_eq_zero_of_head_zero hl
      omega
    | succ k =>
      exact ⟨k + 1, r, rfl, by omega⟩

theorem sum_map_sub_one {l : List ℕ} (hpos : ∀ x ∈ l, 1 ≤ x) :
    (l.map (· - 1)).sum + l.length = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ a := hpos a (by simp)
    have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => hpos x (by simp [hx])
    have := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sum_phiStep {d : ℕ} {r : List ℕ} (hd : d ≤ r.length) (hpos : ∀ x ∈ r.take d, 1 ≤ x) :
    (phiStep d r).sum + d = r.sum := by
  have hperm : (phiStep d r).Perm ((r.take d).map (· - 1) ++ r.drop d) :=
    List.mergeSort_perm _ _
  rw [hperm.sum_eq, List.sum_append]
  have h1 := sum_map_sub_one hpos
  have hlen : (r.take d).length = d := List.length_take_of_le hd
  have h2 : (r.take d).sum + (r.drop d).sum = r.sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

theorem sum_eq_of_coe_eq {l₁ l₂ : List ℕ} (h : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) :
    l₁.sum = l₂.sum :=
  (Multiset.coe_eq_coe.mp h).sum_eq

theorem length_eq_of_coe_eq {l₁ l₂ : List ℕ} (h : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) :
    l₁.length = l₂.length :=
  (Multiset.coe_eq_coe.mp h).length_eq

theorem countP_ge_le_of_lt {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {idx c : ℕ} (hidx : idx < l.length) (hlt : l[idx] < c) :
    ((l : Multiset ℕ).filter (c ≤ ·)).card ≤ idx := by
  have hsplit : (l : Multiset ℕ) = ((l.take idx : List ℕ) : Multiset ℕ) +
      ((l.drop idx : List ℕ) : Multiset ℕ) := by
    conv_lhs => rw [← List.take_append_drop idx l]
    rfl
  rw [hsplit, Multiset.filter_add, Multiset.card_add]
  have hdrop : Multiset.filter (c ≤ ·) ((l.drop idx : List ℕ) : Multiset ℕ) = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    rw [Multiset.mem_filter, Multiset.mem_coe] at hx
    obtain ⟨hmem, hcx⟩ := hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    have hidxk : idx + k < l.length := by
      rw [List.length_drop] at hk; omega
    have heq : (l.drop idx)[k] = l[idx + k] := List.getElem_drop
    rw [heq] at hcx
    have hle : l[idx + k] ≤ l[idx] := getElem_ge_of_pairwise_ge hl hidx hidxk (by omega)
    omega
  rw [hdrop, Multiset.card_zero, add_zero]
  have h1 : (Multiset.filter (c ≤ ·) ((l.take idx : List ℕ) : Multiset ℕ)).card ≤
      Multiset.card ((l.take idx : List ℕ) : Multiset ℕ) :=
    Multiset.card_le_card (Multiset.filter_le _ _)
  simpa [List.length_take_of_le (Nat.le_of_lt hidx)] using h1

theorem le_getElem_of_filter_card_ge {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {idx c : ℕ} (hidx : idx < l.length)
    (hcard : idx + 1 ≤ ((l : Multiset ℕ).filter (c ≤ ·)).card) :
    c ≤ l[idx] := by
  by_contra hlt
  push Not at hlt
  have := countP_ge_le_of_lt hl hidx hlt
  omega

/-! ## 4. First / Last Occurrence and In-Place Sorted `List.set` -/

theorem exists_last_idx {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) {v : ℕ} (hv : v ∈ l) :
    ∃ (r : ℕ) (hr : r < l.length),
      l[r]'hr = v ∧ ∀ k, r < k → (hk : k < l.length) → l[k]'hk < v := by
  induction l with
  | nil => cases hv
  | cons a t ih =>
    have ⟨ha_ge, ht_pw⟩ := List.pairwise_cons.mp hl
    by_cases hvt : v ∈ t
    · obtain ⟨r, hr, hval, hlast⟩ := ih ht_pw hvt
      refine ⟨r + 1, by simp; omega, by simp [hval], ?_⟩
      intro k hk hkl
      cases k with
      | zero => omega
      | succ k' =>
        simp only [List.getElem_cons_succ]
        exact hlast k' (by omega) (by simp at hkl; omega)
    · have hav : a = v := by
        rcases List.mem_cons.mp hv with rfl | hmem
        · rfl
        · exact absurd hmem hvt
      subst hav
      refine ⟨0, by simp, by simp, ?_⟩
      intro k hk hkl
      cases k with
      | zero => omega
      | succ k' =>
        simp only [List.getElem_cons_succ]
        have hk' : k' < t.length := by simp at hkl; omega
        have hmem : t[k'] ∈ t := List.getElem_mem hk'
        have hle : t[k'] ≤ a := ha_ge _ hmem
        have hne : t[k'] ≠ a := fun heq => hvt (heq ▸ hmem)
        omega

theorem exists_first_idx {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) {v : ℕ} (hv : v ∈ l) :
    ∃ (i : ℕ) (hi : i < l.length),
      l[i]'hi = v ∧ ∀ k, k < i → (hk : k < l.length) → v < l[k]'hk := by
  induction l with
  | nil => cases hv
  | cons a t ih =>
    have ⟨ha_ge, ht_pw⟩ := List.pairwise_cons.mp hl
    by_cases hav : a = v
    · subst hav
      exact ⟨0, by simp, by simp, fun k hk _ => by omega⟩
    · have hvt : v ∈ t := by
        rcases List.mem_cons.mp hv with rfl | hmem
        · exact absurd rfl hav
        · exact hmem
      have hva : v < a := by
        have hle := ha_ge v hvt
        omega
      obtain ⟨i, hi, hval, hfirst⟩ := ih ht_pw hvt
      refine ⟨i + 1, by simp; omega, by simp [hval], ?_⟩
      intro k hk hkl
      cases k with
      | zero => simpa using hva
      | succ k' =>
        simp only [List.getElem_cons_succ]
        exact hfirst k' (by omega) (by simp at hkl; omega)

theorem coe_set_cons (l : List ℕ) {idx : ℕ} (hidx : idx < l.length) (y : ℕ) :
    l[idx] ::ₘ ((l.set idx y : List ℕ) : Multiset ℕ) = y ::ₘ (l : Multiset ℕ) := by
  induction l generalizing idx with
  | nil => simp at hidx
  | cons a t ih =>
    cases idx with
    | zero =>
      change a ::ₘ (y ::ₘ (t : Multiset ℕ)) = y ::ₘ (a ::ₘ (t : Multiset ℕ))
      exact Multiset.cons_swap a y (t : Multiset ℕ)
    | succ k =>
      have hk : k < t.length := by simp at hidx; omega
      change t[k] ::ₘ (a ::ₘ ((t.set k y : List ℕ) : Multiset ℕ)) =
        y ::ₘ (a ::ₘ (t : Multiset ℕ))
      rw [Multiset.cons_swap t[k] a, ih hk, Multiset.cons_swap y a]

theorem coe_set_eq_of_coe_cons {l : List ℕ} {idx v y : ℕ} {m : Multiset ℕ}
    (hidx : idx < l.length) (hval : l[idx] = v) (hcoe : (l : Multiset ℕ) = v ::ₘ m) :
    ((l.set idx y : List ℕ) : Multiset ℕ) = y ::ₘ m := by
  have h := coe_set_cons l hidx y
  rw [hval, hcoe, Multiset.cons_swap y v m] at h
  exact (Multiset.cons_inj_right v).mp h

theorem pairwise_set_dec_last {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {r v : ℕ} (hr : r < l.length) (hval : l[r] = v)
    (hlast : ∀ k, r < k → (hk : k < l.length) → l[k] < v) :
    (l.set r (v - 1)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_set] at hi hj
  rw [List.getElem_set, List.getElem_set]
  split_ifs with h1 h2 h3
  · omega
  · have hlt : l[j] < v := hlast j (by omega) hj
    omega
  · subst h3
    have hle : l[r] ≤ l[i] := getElem_ge_of_pairwise_ge hl hi hj (by omega)
    omega
  · exact getElem_ge_of_pairwise_ge hl hi hj (by omega)

theorem pairwise_set_inc_first {l : List ℕ} (hl : l.Pairwise (· ≥ ·))
    {i u : ℕ} (hi : i < l.length) (hval : l[i] = u)
    (hfirst : ∀ k, k < i → (hk : k < l.length) → u < l[k]) :
    (l.set i (u + 1)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [List.length_set] at ha hb
  rw [List.getElem_set, List.getElem_set]
  split_ifs with h1 h2 h3
  · omega
  · subst h1
    have hle : l[b] ≤ l[i] := getElem_ge_of_pairwise_ge hl ha hb (by omega)
    omega
  · have hlt : u < l[a] := hfirst a (by omega) ha
    omega
  · exact getElem_ge_of_pairwise_ge hl ha hb (by omega)

theorem eq_set_dec_last_of_singleDec {M M' : List ℕ} {v : ℕ} {R : Multiset ℕ}
    (hM : M.Pairwise (· ≥ ·)) (hM' : M'.Pairwise (· ≥ ·))
    (hM_eq : (M : Multiset ℕ) = v ::ₘ R)
    (hM'_eq : (M' : Multiset ℕ) = (v - 1) ::ₘ R) :
    ∃ (r : ℕ) (hr : r < M.length),
      M[r]'hr = v ∧
      (∀ k, r < k → (hk : k < M.length) → M[k]'hk < v) ∧
      M' = M.set r (v - 1) := by
  have hvM : v ∈ M := by
    rw [← Multiset.mem_coe, hM_eq]
    exact Multiset.mem_cons_self v R
  obtain ⟨r, hr, hval, hlast⟩ := exists_last_idx hM hvM
  have hpw := pairwise_set_dec_last hM hr hval hlast
  have hcoe := coe_set_eq_of_coe_cons hr hval hM_eq (y := v - 1)
  have hEq : M' = M.set r (v - 1) :=
    eq_of_coe_eq_of_pairwise hM' hpw (by rw [hM'_eq, hcoe])
  exact ⟨r, hr, hval, hlast, hEq⟩

theorem length_eq_of_singleDec {M M' : List ℕ} {v : ℕ} {R : Multiset ℕ}
    (hM_eq : (M : Multiset ℕ) = v ::ₘ R)
    (hM'_eq : (M' : Multiset ℕ) = (v - 1) ::ₘ R) :
    M'.length = M.length := by
  have hc₁ : M.length = (v ::ₘ R).card := by
    rw [← Multiset.coe_card, hM_eq]
  have hc₂ : M'.length = ((v - 1) ::ₘ R).card := by
    rw [← Multiset.coe_card, hM'_eq]
  simp only [Multiset.card_cons] at hc₁ hc₂
  omega

theorem getElem_le_of_singleDec {M M' : List ℕ} {v : ℕ} {R : Multiset ℕ}
    (hM : M.Pairwise (· ≥ ·)) (hM' : M'.Pairwise (· ≥ ·))
    (hM_eq : (M : Multiset ℕ) = v ::ₘ R)
    (hM'_eq : (M' : Multiset ℕ) = (v - 1) ::ₘ R)
    {i : ℕ} (hi : i < M.length) (hi' : i < M'.length) :
    M'[i]'hi' ≤ M[i]'hi := by
  obtain ⟨r, hr, hval, _, rfl⟩ := eq_set_dec_last_of_singleDec hM hM' hM_eq hM'_eq
  rw [List.getElem_set]
  split_ifs with h
  · subst h; omega
  · exact le_rfl

theorem getD_eq_getElem_nat (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    l.getD i 0 = l[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem getD_eq_zero_of_ge (l : List ℕ) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_le_of_singleDec {M M' : List ℕ} {v : ℕ} {R : Multiset ℕ}
    (hM : M.Pairwise (· ≥ ·)) (hM' : M'.Pairwise (· ≥ ·))
    (hM_eq : (M : Multiset ℕ) = v ::ₘ R)
    (hM'_eq : (M' : Multiset ℕ) = (v - 1) ::ₘ R) (i : ℕ) :
    M'.getD i 0 ≤ M.getD i 0 := by
  have hlen := length_eq_of_singleDec hM_eq hM'_eq
  by_cases hi : i < M.length
  · have hi' : i < M'.length := by omega
    rw [getD_eq_getElem_nat M' hi', getD_eq_getElem_nat M hi]
    exact getElem_le_of_singleDec hM hM' hM_eq hM'_eq hi hi'
  · have hi' : M'.length ≤ i := by omega
    rw [getD_eq_zero_of_ge M' hi', getD_eq_zero_of_ge M (by omega)]

/-! ## 5. `List.set` Interaction with `take` / `drop` and Lemma 0(2) -/

theorem take_set_of_lt (l : List ℕ) {r d y : ℕ} (hrd : r < d) :
    (l.set r y).take d = (l.take d).set r y := by
  induction l generalizing r d with
  | nil => simp
  | cons a t ih =>
    cases d with
    | zero => omega
    | succ d' =>
      cases r with
      | zero => simp
      | succ r' =>
        simp only [List.set_cons_succ, List.take_succ_cons]
        congr 1
        exact ih (by omega)

theorem drop_set_of_lt (l : List ℕ) {r d y : ℕ} (hrd : r < d) :
    (l.set r y).drop d = l.drop d := by
  induction l generalizing r d with
  | nil => simp
  | cons a t ih =>
    cases d with
    | zero => omega
    | succ d' =>
      cases r with
      | zero => simp
      | succ r' =>
        simp only [List.set_cons_succ, List.drop_succ_cons]
        exact ih (by omega)

theorem take_set_of_ge (l : List ℕ) {r d y : ℕ} (hdr : d ≤ r) :
    (l.set r y).take d = l.take d := by
  induction l generalizing r d with
  | nil => simp
  | cons a t ih =>
    cases d with
    | zero => simp
    | succ d' =>
      cases r with
      | zero => omega
      | succ r' =>
        simp only [List.set_cons_succ, List.take_succ_cons]
        congr 1
        exact ih (by omega)

theorem drop_set_of_ge (l : List ℕ) {r d y : ℕ} (hdr : d ≤ r) :
    (l.set r y).drop d = (l.drop d).set (r - d) y := by
  induction l generalizing r d with
  | nil => simp
  | cons a t ih =>
    cases d with
    | zero => simp
    | succ d' =>
      cases r with
      | zero => omega
      | succ r' =>
        simp only [List.set_cons_succ, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
        exact ih (by omega)

/-- **Lemma 0(2) (Single-Decrement Commutation with `Φ_d`):**
Decrementing one entry `v ≥ 1` in a descending sorted list `M` of length `≥ d` commutes with
`phiStep d`, decrementing a single entry `w ≥ 1` of `phiStep d M`, with either:
- `w = v - 1` and `M'.drop d = M.drop d` (when the decremented slot lies in the top `d`), or
- `w = v ≤ M.getD d 0` and `v ∈ M.drop d` (when the decremented slot lies at index `≥ d`). -/
theorem phiStep_singleDec
    {M M' : List ℕ} {d v : ℕ} {R : Multiset ℕ}
    (hM : M.Pairwise (· ≥ ·)) (hM' : M'.Pairwise (· ≥ ·))
    (hd : d ≤ M.length)
    (hposM' : ∀ z ∈ M'.take d, 1 ≤ z)
    (hv : 1 ≤ v)
    (hM_eq : (M : Multiset ℕ) = v ::ₘ R)
    (hM'_eq : (M' : Multiset ℕ) = (v - 1) ::ₘ R) :
    ∃ (w : ℕ) (T : Multiset ℕ),
      1 ≤ w ∧
      (phiStep d M : Multiset ℕ) = w ::ₘ T ∧
      (phiStep d M' : Multiset ℕ) = (w - 1) ::ₘ T ∧
      ((w = v - 1 ∧ M'.drop d = M.drop d) ∨
       (w = v ∧ w ≤ M.getD d 0 ∧ v ∈ M.drop d)) := by
  obtain ⟨r, hr, hval, _, hM'_set⟩ := eq_set_dec_last_of_singleDec hM hM' hM_eq hM'_eq
  by_cases hrd : r < d
  · -- Decremented slot lies in `take d`
    have hr_take : r < (M.take d).length := by
      rw [List.length_take_of_le hd]; exact hrd
    have hM'_take : M'.take d = (M.take d).set r (v - 1) := by
      rw [hM'_set, take_set_of_lt M hrd]
    have hM'_drop : M'.drop d = M.drop d := by
      rw [hM'_set, drop_set_of_lt M hrd]
    have hv1 : 1 ≤ v - 1 := by
      have hmem : v - 1 ∈ M'.take d := by
        rw [hM'_take]
        have hr_len : r < ((M.take d).set r (v - 1)).length := by
          rw [List.length_set]; exact hr_take
        have hgm := List.getElem_mem hr_len
        simpa using hgm
      exact hposM' (v - 1) hmem
    have hmap_len : r < ((M.take d).map (· - 1)).length := by
      rw [List.length_map]; exact hr_take
    have hmap_val : ((M.take d).map (· - 1))[r]'hmap_len = v - 1 := by
      simp [List.getElem_take, hval]
    have hmap_set : (M'.take d).map (· - 1) =
        ((M.take d).map (· - 1)).set r ((v - 1) - 1) := by
      rw [hM'_take, List.map_set]
    have hcoe_map := coe_set_cons ((M.take d).map (· - 1)) hmap_len ((v - 1) - 1)
    rw [hmap_val, ← hmap_set] at hcoe_map
    have hmem_map : v - 1 ∈ (((M.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
      rw [Multiset.mem_coe, ← hmap_val]
      exact List.getElem_mem hmap_len
    obtain ⟨T₀, hT₀⟩ := Multiset.exists_cons_of_mem hmem_map
    have hT₀' : (((M'.take d).map (· - 1) : List ℕ) : Multiset ℕ) = ((v - 1) - 1) ::ₘ T₀ := by
      rw [hT₀, Multiset.cons_swap ((v - 1) - 1) (v - 1) T₀] at hcoe_map
      exact (Multiset.cons_inj_right (v - 1)).mp hcoe_map
    refine ⟨v - 1, T₀ + (M.drop d : Multiset ℕ), hv1, ?_, ?_, Or.inl ⟨rfl, hM'_drop⟩⟩
    · rw [coe_phiStep, ← Multiset.coe_add, hT₀, Multiset.cons_add]
    · rw [coe_phiStep, ← Multiset.coe_add, hT₀', hM'_drop, Multiset.cons_add]
  · -- Decremented slot lies in `drop d`
    have hdr : d ≤ r := Nat.le_of_not_lt hrd
    have hM'_take : M'.take d = M.take d := by
      rw [hM'_set, take_set_of_ge M hdr]
    have hM'_drop : M'.drop d = (M.drop d).set (r - d) (v - 1) := by
      rw [hM'_set, drop_set_of_ge M hdr]
    have hr_drop : r - d < (M.drop d).length := by
      rw [List.length_drop]; omega
    have hdrop_val : (M.drop d)[r - d]'hr_drop = v := by
      rw [List.getElem_drop]
      have : d + (r - d) = r := by omega
      simp [this, hval]
    have hv_drop : v ∈ M.drop d := by
      rw [← hdrop_val]
      exact List.getElem_mem hr_drop
    have hd_lt : d < M.length := by omega
    have hv_le : v ≤ M.getD d 0 := by
      rw [getD_eq_getElem_nat M hd_lt, ← hval]
      exact getElem_ge_of_pairwise_ge hM hd_lt hr hdr
    have hcoe_drop := coe_set_cons (M.drop d) hr_drop (v - 1)
    rw [hdrop_val, ← hM'_drop] at hcoe_drop
    have hmem_drop : v ∈ (M.drop d : Multiset ℕ) := Multiset.mem_coe.mpr hv_drop
    obtain ⟨T₀, hT₀⟩ := Multiset.exists_cons_of_mem hmem_drop
    have hT₀' : (M'.drop d : Multiset ℕ) = (v - 1) ::ₘ T₀ := by
      rw [hT₀, Multiset.cons_swap (v - 1) v T₀] at hcoe_drop
      exact (Multiset.cons_inj_right v).mp hcoe_drop
    refine ⟨v, (((M.take d).map (· - 1) : List ℕ) : Multiset ℕ) + T₀, hv, ?_, ?_,
      Or.inr ⟨rfl, hv_le, hv_drop⟩⟩
    · rw [coe_phiStep, ← Multiset.coe_add, hT₀, Multiset.add_cons]
    · rw [coe_phiStep, ← Multiset.coe_add, hM'_take, hT₀', Multiset.add_cons]

end WOWII61.ResidueSeq
