module

public import WOWII61.MatchingDiameter
public import WOWII61.ResidueFoundation
public import WOWII61.ResidueSeqMonotone

public section

namespace WOWII61

/-- Deleting a positive maximum-degree vertex preserves or increases Havel–Hakimi residue. -/
theorem positiveMaximumDeletion : PackingBound.MaxDegDeletionResiduePremise :=
  maxDegreeDeletion_of_exchange ResidueSeq.residueAux_le_of_exchangeStep

/-- Some residue-sized independent set avoids one entire side of any induced matching. -/
theorem inducedMatchingResidue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (M : PackingForest.InducedMatching G k) :
    SimpleGraph.residue G ≤ max (G.induce { u : V | u ∉ M.A }).indepNum
      (G.induce { u : V | u ∉ M.B }).indepNum :=
  MatchingResidue.imr_of_maxDegDeletion G M positiveMaximumDeletion

/-- Natural-valued WOWII Conjecture 61 for every finite connected graph (including singletons). -/
theorem natForestBound {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize :=
  MatchingResidue.wowii61_of_maxDegDeletion G h positiveMaximumDeletion

/-- The induced-forest inequality with the casts and integer ceiling of the 2004 conjecture. -/
theorem realForestBound {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (SimpleGraph.residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) :=
  realBoundOfMaxDegreeDeletion positiveMaximumDeletion G h

end WOWII61
