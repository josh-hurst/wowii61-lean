# Written on the Wall II, Conjecture 61 — Lean 4 Proof

A complete, premise-free Lean 4 / Mathlib formalization proving **Written on the Wall II Conjecture 61** (E. DeLaViña, Graffiti.pc, 25 March 2004):

> For every nontrivial finite connected simple graph $G$,
> $$f(G) \ge R(G) + \left\lceil \frac{\operatorname{diam}(G)}{3} \right\rceil,$$
> where $f(G)$ is the order of a largest induced forest, $R(G)$ is the Havel–Hakimi residue, and $\operatorname{diam}(G)$ is the diameter of $G$.

Along the way, the repository proves a general theorem for arbitrary finite simple graphs (strictly generalizing Favaron–Mahéo–Saclé 1991, $R(G) \le \alpha(G)$):

> **Induced-Matching Residue Inequality:** For every finite simple graph $G$ and every induced matching between disjoint independent vertex sets $A$ and $B$,
> $$R(G) \le \max\big(\alpha(G - A),\; \alpha(G - B)\big).$$

## Main Formalized Declarations

Both declarations are stated in [`Challenge.lean`](Challenge.lean), proved in [`Solution.lean`](Solution.lean), and verified by [`comparator.json`](comparator.json) using only the three standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`):

- **`WrittenOnTheWallII.GraphConjecture61.conjecture61`** — exact upstream statement from [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean).
- **`WrittenOnTheWallII.GraphConjecture61.induced_matching_residue`** — the general Induced-Matching Residue Inequality for arbitrary finite simple graphs.
- **`WOWII61.natForestBound`** (in [`WOWII61/Main.lean`](WOWII61/Main.lean)) — natural-number form `R(G) + (diam(G) + 2) / 3 ≤ f(G)` covering all finite connected graphs including singletons ($n = 1$).

## Proof Overview

1. **Positive maximum-degree deletion monotonicity** ([`WOWII61/ResidueSeqMonotone.lean`](WOWII61/ResidueSeqMonotone.lean), [`WOWII61/GraphToHH.lean`](WOWII61/GraphToHH.lean), [`WOWII61/MaxDegBridge.lean`](WOWII61/MaxDegBridge.lean)): Proved from first principles in Lean 4 via Havel–Hakimi sequence dominance/exchange monotonicity: for every finite simple graph $Q$ and every maximum-degree vertex $v$ of positive degree, $R(Q) \le R(Q - v)$.
2. **Matching-residue induction & IMR** ([`WOWII61/MatchingResidue.lean`](WOWII61/MatchingResidue.lean)): Let $K$ be a graph with disjoint vertex sets $A, B$ whose union is independent in $K$, and let $T = K + (A \times B)$. Inducting on $|V(K)|$ with $|A| \le |B|$ shows there exists a matching $M$ of size $|A|$ between $A$ and $B$ with $R(K + M) \le \alpha(T)$ (either a maximum-degree vertex outside $B$ is deleted, or the independent set $S \subseteq B$ attaining $\max_{b \in B} \deg_K(b)$ is deleted sequentially with matched vertices first). Removing an induced matching $M_0$ from $G$ gives $K$ with $R(K + M) = R(G)$ for every perfect matching $M$, yielding $R(G) \le \alpha(T) = \max(\alpha(G - A), \alpha(G - B))$.
3. **Diametral star-packing lift** ([`WOWII61/PackingForest.lean`](WOWII61/PackingForest.lean), [`WOWII61/MatchingDiameter.lean`](WOWII61/MatchingDiameter.lean), [`WOWII61/CeilingBound.lean`](WOWII61/CeilingBound.lean)): Along a diametral geodesic $v_0, \dots, v_D$, the $k = \lceil D/3 \rceil$ edges $v_{3i}v_{3i+1}$ ($0 \le i < k$) form an induced matching whose sides $A, B$ are each $3$-packings. IMR supplies an independent set $I$ of size $\ge R(G)$ disjoint from one side $W \in \{A, B\}$; every vertex of $I$ has at most one neighbor in $W$, so $G[I \cup W]$ is a forest of at least $R(G) + \lceil D/3 \rceil$ vertices.

## Verification

Toolchain: `leanprover/lean4:v4.35.0-rc2` with Mathlib pinned in [`lake-manifest.json`](lake-manifest.json).

```sh
lake exe cache get
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake --wfail build
lake env leanchecker -v --fresh Solution
./scripts/verify-comparator.sh   # Linux with bubblewrap
```

## License & Registry

Licensed under Apache-2.0 (retaining upstream Apache-2.0 notices from Google DeepMind's Formal Conjectures repository; see [`LICENSE`](LICENSE)). Registry submissions go to <https://submit.palomar-registry.org/>.
