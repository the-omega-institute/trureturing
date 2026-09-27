# The Unlucky-Car Spectrum of Stirling Permutations

## Abstract

Every count of unlucky cars allowed by the bound is attained by a Stirling permutation.

**Definition 1.1 (Walking up to a free spot).**

$$\forall occ \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall s \in \mathrm{Nat},\; \forall f \in \mathrm{Nat},\; \operatorname{freeFrom}\left(0, occ, s\right) = s   ((s \in occ) \Rightarrow (\operatorname{freeFrom}\left(f + 1, occ, s\right) = \operatorname{freeFrom}\left(f, occ, s + 1\right))) \land ((\neg (s \in occ)) \Rightarrow (\operatorname{freeFrom}\left(f + 1, occ, s\right) = s))$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.freeFrom` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

A bounded upward search: from the spot s, move on while the spot is taken, and stop after at most f moves. The bound f is supplied by the caller and is chosen below so that the search always stops at a free spot.

**Definition 1.2 (A bound for the occupied spots).**

$$\forall occ \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall p \in \mathrm{Nat},\; \operatorname{occBound}\left(occ, p\right) = \operatorname{foldr}\left(max, p, occ\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.occBound` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

The largest of p and the entries of occ. Every occupied spot is at most this value, so the first free spot at or after p is at most one more than it.

**Definition 1.3 (The spot a car takes).**

$$\forall occ \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall p \in \mathrm{Nat},\; \operatorname{firstFree}\left(occ, p\right) = \operatorname{freeFrom}\left(\operatorname{occBound}\left(occ, p\right) + 1, occ, p\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.firstFree` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

The source has each car drive to its preferred spot and then continue forward to the first free spot. Running the upward search with one more step than the bound of the occupied spots reaches that spot in every case: if p exceeds every occupied spot the search stops at once, and otherwise the first free spot at or after p is at most the bound plus one, which is within reach.

**Definition 1.4 (Parking the cars in order).**

$$\forall occ \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall p \in \mathrm{Nat},\; \forall ps \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{parkAux}\left([], occ\right) = []   \operatorname{parkAux}\left(p :: ps, occ\right) = \operatorname{firstFree}\left(occ, p\right) :: \operatorname{parkAux}\left(ps, \operatorname{firstFree}\left(occ, p\right) :: occ\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.parkAux` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

Cars enter one at a time, each taking the first free spot at or after the one it prefers, and the list records the spot each car takes.

**Definition 1.5 (Parking on an empty lot).**

$$\forall w \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{spots}\left(w\right) = \operatorname{parkAux}\left(w, []\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.spots` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

The parking outcome of the word w, read as a preference list on an initially empty lot with spots numbered from one.

**Definition 1.6 (The displacement composition).**

$$\forall w \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{dis}\left(w\right) = \operatorname{zipWith}\left((s, p) \mapsto s - p, \operatorname{spots}\left(w\right), w\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.dis` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

Definition 39 of the source: the tuple whose entry for each car is the spot the car takes minus the spot it prefers. A car is lucky exactly when its entry is zero, so the number of nonzero entries is the number of unlucky cars. Every Stirling permutation is a parking function, so each entry is a difference of a larger spot from a smaller preference.

**Definition 1.7 (Counting the unlucky cars).**

$$\forall w \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{displaced}\left(w\right) = \operatorname{countP}\left(d \mapsto d \ne 0, \operatorname{dis}\left(w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.displaced` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

The number of nonzero entries of the displacement composition. Corollary 41 of the source bounds this count between n and 2n minus one for every Stirling permutation of order n, because the number of lucky cars lies between one and n.

**Definition 1.8 (Stirling permutations).**

$$\forall n \in \mathrm{Nat},\; \forall w \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{IsStirling}\left(n, w\right)) \Leftrightarrow ((\operatorname{length}\left(w\right) = 2 \cdot n) \land ((\forall v \in \mathrm{Nat},\; (((1 \le v) \land (v \le n)) \Rightarrow (\operatorname{count}\left(w, v\right) = 2)) \land ((\neg ((1 \le v) \land (v \le n))) \Rightarrow (\operatorname{count}\left(w, v\right) = 0))) \land (\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; (u \le v) \Rightarrow (\neg (\operatorname{Sublist}\left([v, u, v], w\right))))))$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.IsStirling` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

Definition 4 of the source reads verbatim: "A permutation of the multiset {1, 1, 2, 2, 3, 3, . . . , n, n} is a Stirling permutation of order n if every value j appearing between the two instances of i satisfies j > i." Being a permutation of that multiset is recorded by the length and by the letter counts, which are two for each value from one to n and zero for every other value. The condition on values between two equal letters is recorded by the absence of a subsequence v, u, v with u at most v: such a subsequence is exactly a value at most i standing between two occurrences of i.

**Definition 1.9 (The question asked of the spectrum).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\forall i \in \mathrm{Nat},\; (n \le i) \Rightarrow ((i \le 2 \cdot n - 1) \Rightarrow (\exists w \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{IsStirling}\left(n, w\right)) \land (\operatorname{displaced}\left(w\right) = i)))))$$

*Formalization.* `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.claim` (`✓ std3`).

*Citation.* Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner (2024). *On the lucky and displacement statistics of Stirling permutations*. DOI: [10.48550/arXiv.2403.03280](https://doi.org/10.48550/arXiv.2403.03280). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html>.

*Commentary.*

Problem 48 of the source reads verbatim: "Determine if, for i in [n, 2n - 1], there exists w in Q_n such that dis(w) has exactly i nonzero entries. Equivalently, can we always find a Stirling permutation with i unlucky cars?" The statement displayed here is the affirmative reading of that question, quantified over every order n at least one and every count i in the stated range.

**Theorem 1.10 (Every allowed count is attained).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/stirling-lucky-displacement-spectrum` (proved) by `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"stirling-lucky-displacement-spectrum","declaration_gid":"D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The answer is yes, by an explicit two-block word. For j from zero to n minus one, take the word that lists the pairs j+1, j+2, up to n in increasing order and then the pairs j, j-1, down to 1 in decreasing order, each value written twice in succession. Equal letters are adjacent, so no value stands between two equal letters and the word is a Stirling permutation of order n. The occupied spots form one interval at every stage of parking. The first car takes spot j+1 and is lucky; each further car of the increasing block finds its preference inside the occupied interval and is pushed to the spot just above it, so after the increasing block the occupied spots are j+1 through 2n-j and exactly one car has been lucky. In the decreasing block the first copy of each value v lands on the free spot v just below the interval and is lucky, while the second copy is pushed to the spot just above it, so each of the j pairs contributes one lucky car and the interval grows by one at each end. The lot ends full, spots 1 through 2n, with j+1 lucky cars and therefore 2n-j-1 nonzero displacement entries. As j runs from zero to n minus one this count runs over every value from n to 2n-1, so choosing j equal to 2n-1-i answers the question for the count i.

## References

- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.IsStirling`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.claim`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.dis`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.displaced`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.firstFree`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.freeFrom`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.occBound`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.parkAux`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result`
- Truth anchor: `D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.spots`
