module

public import WOWII61.MatchingResidue
public import WOWII61.CeilingBound

public section

namespace WOWII61

open SimpleGraph

/-- The matching theorem and the geodesic construction imply the upstream real inequality
from positive maximum-degree deletion for Havel–Hakimi residue. -/
theorem realBoundOfMaxDegreeDeletion (hDel : PackingBound.MaxDegDeletionResiduePremise)
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) :=
  realCeilingBound _ _ _ (MatchingResidue.wowii61_of_maxDegDeletion_nontrivial G h hDel)

end WOWII61
