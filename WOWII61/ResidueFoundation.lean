module

public import WOWII61.MaxDegBridge
public import WOWII61.ResidueSeqDefs

public section

namespace WOWII61

/-- The graph realization and the sequence induction use the same Havel–Hakimi validity test. -/
private theorem seqValid_of_graphValid (s : List ℕ) (h : ResidueGraph.IsHHValid s) :
    ResidueSeq.IsHHValid s := by
  cases s with
  | nil => exact ResidueSeq.isHHValid_nil.mpr trivial
  | cons d rest =>
    obtain ⟨hsize, hpos, hnext⟩ := (ResidueGraph.isHHValid_cons d rest).mp h
    exact (ResidueSeq.isHHValid_cons d rest).mpr
      ⟨hsize, hpos, seqValid_of_graphValid _ hnext⟩
termination_by s.length
decreasing_by
  subst s
  simp [SimpleGraph.havelHakimiStep_length_cons]

/-- Transport elementary-exchange monotonicity to the positive-degree graph deletion theorem. -/
theorem maxDegreeDeletion_of_exchange
    (mono : ∀ {a b : List ℕ}, ResidueSeq.ExchangeStep a b →
      ResidueSeq.IsHHValid a → ResidueSeq.IsHHValid b →
      SimpleGraph.residueAux a ≤ SimpleGraph.residueAux b) :
    PackingBound.MaxDegDeletionResiduePremise :=
  ResidueGraph.maxDegDeletionResiduePremise_of_exchangeStep fun a b hab ha hb =>
    mono hab (seqValid_of_graphValid a ha) (seqValid_of_graphValid b hb)

end WOWII61
