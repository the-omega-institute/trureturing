# Unit-interval parking and Foata transformation

## Abstract

Parking-process specifications, Foata commutation for distinct-letter and nondecreasing words, and a recursive characterisation of unit-interval parking. Conjecture 6.3 remains unproved.

**Definition 1.1 (parkStep).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given occupied spots and a preference, the structural search advances to the first vacant spot at or above that preference.

**Definition 1.2 (parkFrom).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkFrom`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cars in the remaining word park in list order, adding each chosen spot to the occupied list.

**Definition 1.3 (spots).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parking starts with no occupied spots and returns the final spots in car order.

**Definition 1.4 (IsParkingFunction).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsParkingFunction`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsParkingFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every preference and final spot must be between one and the length of the preference word.

**Definition 1.5 (IsUnitInterval).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsUnitInterval`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsUnitInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A parking function is unit interval when each final spot is at most one greater than its corresponding preference.

**Definition 1.6 (rotateBlocks).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.rotateBlocks`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.rotateBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pending list records an unfinished block. A cut moves its closing letter to the front; the recursion then begins the next block.

**Definition 1.7 (foataStep).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foataStep`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foataStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If the previous last letter is at most the new letter, cuts follow letters at most the new letter. Otherwise cuts follow greater letters. Each block is rotated and the new letter is appended.

**Definition 1.8 (foata).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Folding the insertion step from the empty word defines the transformation.

**Theorem 1.9 (parkStep_of_not_mem).**

$$\forall O\in \operatorname{List}(\mathbb{N}),\  \forall p\in \mathbb{N},\quad \neg (p\in O)\Rightarrow \operatorname{parkStep}(O,p)=p$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_of_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupied list and preference absent from that list, the chosen spot equals the preference.

**Theorem 1.10 (le_parkStep).**

$$\forall O\in \operatorname{List}(\mathbb{N}),\  \forall p\in \mathbb{N},\quad p\le \operatorname{parkStep}(O,p)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.le_parkStep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupied list and preference, the chosen spot is at least the preference.

**Theorem 1.11 (parkStep_spec).**

$$\forall O\in \operatorname{List}(\mathbb{N}),\  \forall p\in \mathbb{N},\quad \neg (\operatorname{parkStep}(O,p)\in O)\land (\forall q\in \mathbb{N},\  p\le q\Rightarrow q<\operatorname{parkStep}(O,p)\Rightarrow q\in O)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupied list and preference, the chosen spot is absent from the occupied list. Every spot at least the preference and strictly below the chosen spot belongs to the occupied list.

**Theorem 1.12 (parkStep_le_add_one_iff).**

$$\forall O\in \operatorname{List}(\mathbb{N}),\  \forall p\in \mathbb{N},\quad \operatorname{parkStep}(O,p)\le p+1\iff \neg (p\in O)\lor \neg (p+1\in O)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_le_add_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupied list and preference, displacement is at most one if and only if the preference or its successor is absent from the occupied list.

**Theorem 1.13 (spots_length).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad |\operatorname{spots}(a)|=|a|$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every preference word, its spot word has the same length.

**Theorem 1.14 (foata_perm).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Perm}(\operatorname{foata}(a),a)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word, its transformed word is a permutation of the original word.

**Theorem 1.15 (foata_append_singleton).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \forall x\in \mathbb{N},\quad \operatorname{foata}(a++[x])=\operatorname{foataStep}(\operatorname{foata}(a),x)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_append_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word and new letter, transforming their concatenation equals inserting the new letter into the transformed word.

**Theorem 1.16 (spots_eq_of_nodup).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Nodup}(a)\Rightarrow \operatorname{spots}(a)=a$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_eq_of_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word with no duplicate letters, the spot word equals the preference word.

**Theorem 1.17 (spot_foata_comm).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Nodup}(a)\Rightarrow \operatorname{spots}(\operatorname{foata}(a))=\operatorname{foata}(\operatorname{spots}(a))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spot_foata_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word with no duplicate letters, parking after transformation equals transformation after parking. This theorem requires distinct letters.

**Theorem 1.18 (parkStep_mono).**

$$\forall O,Oprime\in \operatorname{List}(\mathbb{N}),\  \forall p,r\in \mathbb{N},\quad O\subseteq Oprime\Rightarrow p\le r\Rightarrow \operatorname{parkStep}(O,p)\le \operatorname{parkStep}(Oprime,r)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For occupied lists with the first contained in the second and preferences with the first at most the second, the first selected spot is at most the second selected spot.

**Theorem 1.19 (spots_pairwise).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Pairwise}_{\le}(a)\Rightarrow \operatorname{Pairwise}_{\le}(\operatorname{spots}(a))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_pairwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nondecreasing preference word, its spot word is nondecreasing.

**Theorem 1.20 (foata_eq_of_pairwise).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Pairwise}_{\le}(a)\Rightarrow \operatorname{foata}(a)=a$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_eq_of_pairwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nondecreasing word, its Foata transformation equals the word itself.

**Theorem 1.21 (spot_foata_comm_of_pairwise).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{Pairwise}_{\le}(a)\Rightarrow \operatorname{spots}(\operatorname{foata}(a))=\operatorname{foata}(\operatorname{spots}(a))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spot_foata_comm_of_pairwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nondecreasing word, parking after transformation equals transformation after parking. Repeated letters are permitted.

**Definition 1.22 (unitRun).**

Lean statement: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.unitRun`

*Formalization.* `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.unitRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursive unit-interval condition requires each preference to belong to the finite street, each chosen spot to stay within its upper bound, and each displacement to be at most one. It recurses over the remaining cars.

**Theorem 1.23 (isUnitInterval_iff_unitRun).**

$$\forall a\in \operatorname{List}(\mathbb{N}),\quad \operatorname{IsUnitInterval}(a)\iff \operatorname{unitRun}(|a|,[],a)=\operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.isUnitInterval_iff_unitRun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every preference word, being a unit-interval parking function is equivalent to the recursive unit-interval condition evaluating to true from an empty street whose size is the word length.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsParkingFunction`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.IsUnitInterval`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foataStep`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_append_singleton`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_eq_of_pairwise`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.foata_perm`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.isUnitInterval_iff_unitRun`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.le_parkStep`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkFrom`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_le_add_one_iff`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_mono`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_of_not_mem`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.parkStep_spec`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.rotateBlocks`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spot_foata_comm`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spot_foata_comm_of_pairwise`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_eq_of_nodup`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_length`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.spots_pairwise`
- Truth anchor: `D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.unitRun`
