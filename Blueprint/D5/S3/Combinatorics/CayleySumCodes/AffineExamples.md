# Retained constructions and exact corrected examples

## Abstract

AffineExamples in the actual loopless sum graphs.

**Theorem 1.1 (The corrected normal connection set).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The connection is the identity together with every affine negation, over the entire field.

**Theorem 1.2 (The corrected subgroup total codes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite field of odd characteristic whose units square to 1 or -1, the full complement fixing zero is a total perfect code of the actual loopless graph. The F3 and F5 specializations are the two original examples, not a claim for arbitrary q.

**Theorem 1.3 (The precise connectedness distinction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For this actual affine connection, connectedness holds exactly when all units are signs. Thus the F3 example is connected and the F5 example is disconnected. Generation alone is not used as a converse connectedness criterion.

Affine applications of the transversal criteria. Let F be any field and write A=Affine1(F)=Fˣ × F. The multiplication, identity and inverse are (s,b)(t,d)=(st,b+sd), (1,0), and (s,b)⁻¹=(s⁻¹,-s⁻¹b). Associativity is the distributive identity b+s(d+tu)=(b+sd)+(st)u; the identity and inverse laws follow by substitution. Over a finite field A has |Fˣ| |F| elements, via the bijection with Fˣ × F. The subgroup C={(s,0):s∈Fˣ} fixes zero. These are actual group elements and all graphs below use adjacency g≠h and gh∈Y, with no loops.

The affine permutation associated with (s,b) is x↦sx+b, with inverse x↦s⁻¹(x-b). For every a=(s,b), d=(t,c) and x∈F, the permutation of ad sends x to stx+b+sc=s(tx+c)+b. Thus multiplication is composition on the entire field. Equality of two such permutations at 0 gives equality of their offsets; equality at 1 then gives equality of the multipliers, hence equality of the pairs. This establishes faithfulness without a restriction on the characteristic or finiteness of F.

For every s∈Fˣ with s≠1 and every a=(t,b)∈A, a is conjugate to (s,0) exactly when t=s. Conjugation preserves the multiplier because Fˣ is commutative: if u(s,0)=au, cancellation gives s=t. Conversely, conjugating (s,0) by the translation (1,b/(1-s)) gives (s,b); the denominator is nonzero by s≠1. Consequently the full nontranslation conjugacy class of (s,0) is the multiplier fiber {(s,b):b∈F}. For any T⊆Fˣ, let Y_T={(s,b):s∈T}. Its membership is unchanged by conjugation, even when 1∈T; the multiplier-1 fiber is the entire translation subgroup, not the single identity conjugacy class.

Let now F be finite, H≤Fˣ any subgroup, and T⊆Fˣ an actual left transversal of H. Explicitly, for every s∈Fˣ there is exactly one t∈T such that t⁻¹s∈H, equivalently s⁻¹t∈H. Embed H as Ĥ={(s,0):s∈H}≤A. This is a subgroup: multiplication multiplies its two H-multipliers and keeps the offset zero, and inversion replaces s by s⁻¹ and keeps zero. For any a₀∈T∩H, every t∈T∩H equals a₀: both t and a₀ represent the identity H-coset, since their inverses belong to H, so transversal uniqueness identifies them. The subgroup definition and this uniqueness calculation hold over every field, without finiteness, a code or a graph premise; finiteness is imposed only for the code conclusions that follow.

Assume additionally that a₀∈T∩H is not a square in H, meaning there is no v∈H with v²=a₀. Then Ĥ is a total perfect code in CS(A,Y_T). For g=(s,b), take its unique transversal representative t and set h=(s⁻¹t,0). Since t⁻¹s∈H, inversion gives s⁻¹t∈H, so h∈Ĥ, and gh has multiplier t∈T. If g=h, then b=0, s∈H and s²=t. Hence t∈T∩H and t=a₀, contradicting the nonsquare assumption. Thus h is an open neighbor. For any other code neighbor k=(u,0), su∈T, and (su)⁻¹s=u⁻¹∈H. Transversal uniqueness gives su=t, so u=s⁻¹t and k=h. This proves existence and uniqueness for every g, including g∈Ĥ.

The cyclic parameters of Zhang Theorem 5.13 are q=|F|, q-1=s*t with t>1, a generator c of Fˣ, and H=⟨c^s⟩ of order t. The construction uses any specified transversal T with its unique internal representative a₀ a nonsquare of this H. In a cyclic H this condition requires even t; with a₀=c^(s*j), it is precisely that j is odd modulo t. The connection includes every element in each chosen multiplier fiber, including the original full conjugacy classes of the nonidentity multipliers. The preceding calculation applies to these parameters exactly; it does not assert that every normal connection giving a total code belongs to this family.

For every field F, every H≤Fˣ and every subset T⊆Fˣ, define P_{H,T}={(s,b):(s∈T and s∉H) or (s=1 and (s,b)≠(1,0))}. Thus the internal multiplier fiber is removed from Y_T and all nonidentity translations are inserted. P_{H,T} is conjugation invariant: conjugation preserves s, and a conjugate of a nonidentity element is nonidentity, as follows by conjugating back. If F is finite and T is an actual transversal, independently of a nonsquare assumption, it follows directly from the closed-neighborhood definition of PerfectCodeTransversal.IsPerfectCode that Ĥ is a perfect code in CS(A,P_{H,T}), as the following three cases show.

If g=(s,b)∈Ĥ, its closed-neighborhood code vertex is g itself. No other k∈Ĥ can be adjacent: gk has multiplier in H, excluding the first part of P_{H,T}, and if that multiplier equals 1 then both offsets vanish, so gk=1, excluding the nonidentity translation part. If s∈H but b≠0, the unique code neighbor is h=(s⁻¹,0); g≠h and gh=(1,b) is a nonidentity translation. Every code neighbor must use this translation part, forcing its multiplier to s⁻¹; equality g=k is impossible since g∉Ĥ. Finally, if s∉H, take t∈T as above and h=(s⁻¹t,0). Here t∉H, since t and t⁻¹s in H would imply s∈H. Thus gh belongs to the first part of P_{H,T}, and g≠h. Any neighbor using that part has multiplier su=t by transversal uniqueness and hence equals h. A neighbor using the translation part would satisfy su=1 with u∈H, implying s=u⁻¹∈H, a contradiction. These cases exhaust all g and establish the closed-neighborhood uniqueness, with no total-code premise.

The corrected small-field examples use Y={1}∪{(−1,b):b∈F}, rather than a nonsquare multiplier transversal. Assume F is finite, 1≠−1, and every u∈Fˣ satisfies u²=1 or u²=−1. For g=(s,b), the unique total-code neighbor in C is (s⁻¹,0) if b=0 and s²≠1, and (−s⁻¹,0) otherwise. Indeed a neighbor k=(u,0) must either satisfy b=0 and su=1, or su=−1. In the first branch equality g=k would force s²=1, while in the second it would force s²=−1 and b=0. The selected branch excludes each equality; for any competing neighbor the same equations and the alternative s²=±1 force precisely the selected u. This is the full field-domain conclusion of total_code, and does not extend to arbitrary q.

For this Y, connected_iff gives connectedness exactly when every unit is 1 or −1, under 1≠−1. In the necessary direction connected_generates forces the closure of Y to be A, while Y lies in the subgroup of sign multipliers; hence all multipliers are signs. Conversely every affine element is reached from 1: a multiplier −1 is an immediate neighbor, and a multiplier 1 is reached through (−1,0), with the inequalities ensured by 1≠−1. For F₃ the two units are ±1 and both square to 1, so C is a total code and the graph is connected. For F₅ the units are 1,2,3,4 with squares 1,4,4,1=±1; 2 is neither sign, so C is a total code and the graph is disconnected. In either field 1∈Y. In any listed nonsquare-transversal total family, 1∈Y_T would put 1∈T and force a₀=1 by uniqueness in T∩H, contradicting its nonsquareness. Thus the connected F₃ graph refutes the old connected exhaustiveness assertion; the F₅ graph is the separate disconnected example, not a counterexample satisfying a connectedness premise. These applications use the sources and attribution in the cited Ma–Nikandish–Zhang library note, including Zhang arXiv:2210.03336v1, and assert no exhaustive classification.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connected_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.connection_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/AffineExamples.total_code`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers](CodeCentralizers.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
