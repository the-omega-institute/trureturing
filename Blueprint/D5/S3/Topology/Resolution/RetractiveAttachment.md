# RetractiveAttachment

## Abstract

Classical arbitrary-set retractive attachment supplier; original Efimov KPI 0.

The pinned Scribe projection corpus does not contain these new declarations. Each node therefore uses the supported no-formula presentation and records its native projection gap; the exact Lean signature and full ambient parameters are reproduced below. The validated scoped report separately contains the complete kernel statement-v1 ASTs. The scientific source and independent ordinary review are identified in the cited Library note; neither source-level review nor this exposition substitutes for kernel checking.

Universes u v w are independent. All attachment declarations have arbitrary B : Type u, I : Type v, P : I → Type w, [TopologicalSpace B], [∀ i, TopologicalSpace (P i)], and t : ∀ i, P i → B, with only the additional hypotheses displayed. The generic helper eventually_eq_of_no_sequence instead has its own arbitrary X : Type* and [TopologicalSpace X] as displayed. Space t is the literal B ⊕ Σ i, P i with the constructed topology; core t b = Sum.inl b, component t i z = Sum.inr ⟨i,z⟩, collapse t is identity on the core and t i on component i, and basic t U J consists of core U and component points with i ∉ J and t i z ∈ U. multiplicity t b = {i | b ∈ Set.range (t i)}. NoConvergentInjectiveSequence X means ∀ (x : ℕ → X) (b : X), Function.Injective x → ¬ Filter.Tendsto x Filter.atTop (nhds b). In particular I can be empty; nonempty compact Hausdorff zero-dimensional inputs are included without weakening their requested conclusion.

Alexandroff duplicate application. Let K be a topological space and specialize the supplier to B = I = K, P i = Unit with its unique topology, and t i (*) = i. Write lower(x) = Sum.inl x and upper(x) = Sum.inr ⟨x,()⟩ in the literal carrier A = K ⊕ Σ i : K, Unit. The bijection from K × {0,1} sends (x,0) to lower(x) and (x,1) to upper(x); collapse t is the base projection on both copies. The supplier basic t U J consists exactly of lower(U) together with upper(U \ J), where U is open and J is a finite set of coordinates. Each upper point is isolated by its Unit component. The duplicate lower basic neighborhood N(V,x) consists of both copies of the open V containing x, with upper(x) deleted.

Assume K is T1 for the topology correspondence. Given x ∈ U and finite J, set V = U \ ↑(J.erase x). This is open, contains x, and N(V,x) is contained in basic t U J: any surviving upper coordinate lies in U, differs from x, and avoids J.erase x, hence avoids J. Conversely N(V,x) equals basic t V {x}. Together with the upper singletons these two refinements show that the displayed bijection is a homeomorphism for the actual duplicate neighborhood topology. Finite deletion is justified by T1; no such homeomorphism for arbitrary non-T1 K is asserted.

The constant attachment maps are continuous. RetractiveAttachment.compact_space gives compactness of A whenever K is compact. RetractiveAttachment.hausdorff gives Hausdorffness whenever K is T2. RetractiveAttachment.continuous_retraction gives continuity of the actual projection and projection ∘ lower = id. RetractiveAttachment.core_closed_embedding identifies lower(K) as a closed embedded copy with the original K topology. Under T2, RetractiveAttachment.component_clopen_embedding applied to Unit identifies each upper singleton as an actual compact clopen subset. These statements concern the constructed carrier and its topology, rather than additional assumed structure on a duplicate.

Now assume K is simultaneously compact, connected, nontrivial and T2. At the pinned Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679, Topology/Perfect supplies the PerfectSpace instance for a connected nontrivial T1 space; PerfectSpace.univ_preperfect and preperfect_iff_nhds supply a point different from the center in every neighborhood. For a lower basic neighborhood basic t U J at x, apply this to U \ ↑(J.erase x). The resulting y differs from x and avoids all of J, so upper(y) lies in that neighborhood. Upper neighborhoods already meet the upper range at their center. Thus the upper range is dense in A.

RetractiveAttachment.is_clopen_iff gives a clopen lower trace, clopen Unit traces and agreement outside one finite exceptional set. Mathlib Topology/Connected/Clopen.isClopen_iff makes the lower trace empty or all of K. In the empty case only finitely many upper coordinates can occur; in the full case only finitely many upper coordinates can be omitted. Conversely finite upper subsets are clopen by the upper singleton result, and their complements are clopen. Hence the actual clopens of A are precisely finite upper subsets and their complements.

The exact ambient clopen-basis locus is the upper range: for every p : A, [∀ O : Set A, IsOpen O → p ∈ O → ∃ C : Set A, IsClopen C ∧ p ∈ C ∧ C ⊆ O] holds if and only if p ∈ range(upper). At an upper point choose its clopen singleton. At lower(x), choose y ≠ x and the open neighborhood basic t (K \ {y}) ∅, which contains lower(x) but omits lower(y); T1 makes its base trace open. Every clopen containing lower(x) contains the entire lower copy by the preceding classification, so none refines this neighborhood. This is a failure of clopen refinements in the ambient A, with all open O and actual subsets C quantified as displayed. Mathlib zeroDimensionalSpace_iff_isTopologicalBasis_isClopen (equivalently zeroDimensionalSpace_iff_nhds_hasBasis_isClopen) therefore rules out ZeroDimensionalSpace A.

For the full two-sphere take K = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1), the entire radius-one sphere in real three-dimensional Euclidean space, with its subspace topology. Mathlib Metric.isCompact_sphere and Metric.sphere.compactSpace give compactness in this finite-dimensional proper metric space; T2 is inherited. The pinned isPathConnected_sphere, hence isConnected_sphere, applies since the real dimension is three and the radius is positive, supplying ConnectedSpace for the sphere subtype. The distinct actual unit coordinate vectors (1,0,0) and (0,1,0) both belong to the sphere, supplying Nontrivial and Nonempty on this same K. All preceding hypotheses thus hold simultaneously for this full sphere, and the duplicate correspondence, compact Hausdorff retraction, closed lower sphere, dense upper range, exact upper clopen-basis locus and failure of zero-dimensionality apply to it. Empty and singleton bases do not satisfy nontriviality; disconnected bases do not satisfy connectedness, and the joint density and clopen-classification conclusions above are not extended to those cases. This application supplies topology only; it infers no bundle, winding, matrix or physical realization statement.

**Theorem 1.1 (Literal neighborhood topology).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.is_open_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.is_open_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem is_open_iff (s : Set (Space t)) : IsOpen s ↔     (∀ i, IsOpen (component t i ⁻¹' s)) ∧     ∀ b, core t b ∈ s → ∃ U, IsOpen U ∧ b ∈ U ∧ ∃ J : Finset I, basic t U J ⊆ s

Space(t) is literally the disjoint union B plus Sigma i P(i). An open set has open component traces and at each included core point contains N(U,J), where U is open and J is a finite set of arbitrary indices. No countability restriction is imposed, and the index type may be empty. The maps t(i) retain their full dependence on the component point.

**Theorem 1.2 (Compactness of the constructed topology).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.compact_space`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.compact_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem compact_space [CompactSpace B] [∀ i, CompactSpace (P i)] : CompactSpace (Space t)

An open cover has a finite subcover on the continuous image of the compact core. The union W of that finite family contains every component outside one finite exceptional set: cover the core by the actual core neighborhoods in W and unite their exceptions. Compactness of each remaining component supplies its finite subcover. Compactness is proved from this topology, not supplied in a structure field.

**Theorem 1.3 (Hausdorff separation).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.hausdorff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.hausdorff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem hausdorff (ht : ∀ i, Continuous (t i)) [T2Space B] [∀ i, T2Space (P i)] :     T2Space (Space t)

Two core points separate by pullbacks of disjoint core opens. A core point and a component separate by omitting that component. Points in one component separate by its open images, and distinct components separate by their clopen ranges.

**Theorem 1.4 (Actual closed core embedding).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.core_closed_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.core_closed_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem core_closed_embedding (ht : ∀ i, Continuous (t i)) : IsClosedEmbedding (core t)

The literal core inclusion is continuous and injective. The core complement is open by the defining topology, and the actual continuous left inverse gives the embedding with the original core topology.

**Theorem 1.5 (Actual compact clopen component embeddings).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.component_clopen_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.component_clopen_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem component_clopen_embedding (i : I) [CompactSpace (P i)] [T2Space B] [∀ i, T2Space (P i)]     (ht : ∀ i, Continuous (t i)) :     IsClosedEmbedding (component t i) ∧ IsClopen (range (component t i)) ∧       IsCompact (range (component t i))

The literal component inclusion is continuous and injective with its original topology. Open subsets of a component are open in the carrier, and the complement of the entire component is N(B,{i}). Each component is therefore an actual compact clopen embedded copy.

**Theorem 1.6 (The literal continuous retraction).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.continuous_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.continuous_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem continuous_retraction (ht : ∀ i, Continuous (t i)) :     Continuous (collapse t) ∧ LeftInverse (collapse t) (core t)

collapse is identity on the literal core and t(i) on component i. The inverse image of U is exactly N(U,empty), so continuity follows for every given continuous attachment map. Neither constancy nor surjectivity is required.

**Theorem 1.7 (Exact finite-defect clopen algebra).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.is_clopen_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.is_clopen_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem is_clopen_iff [CompactSpace B] (ht : ∀ i, Continuous (t i)) (H : Set (Space t)) :     IsClopen H ↔ IsClopen (core t ⁻¹' H) ∧       (∀ i, IsClopen (component t i ⁻¹' H)) ∧       ∃ J : Finset I, ∀ i, i ∉ J → component t i ⁻¹' H = t i ⁻¹' (core t ⁻¹' H)

Write V for the inverse image along the literal core inclusion and H(i) for the component trace. A clopen H has clopen traces. The open agreement set (H intersect collapse inverse V) union (complement H intersect collapse inverse complement V) contains the whole core. Compactness gives finitely many exceptional components; all other traces equal t(i) inverse V. Conversely the clopen traces and that one finite exception set give open core neighborhoods for H and its complement. This is an equivalence for actual subsets, including empty traces.

**Theorem 1.8 (A genuine clopen basis).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.zero_dimensional`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.zero_dimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem zero_dimensional [CompactSpace B] [T2Space B] [ZeroDimensionalSpace B]     [∀ i, CompactSpace (P i)] [∀ i, T2Space (P i)] [∀ i, ZeroDimensionalSpace (P i)]     (ht : ∀ i, Continuous (t i)) : ZeroDimensionalSpace (Space t)

At a core point refine its actual open core neighborhood by a core clopen and retain the finite omissions. The finite-defect theorem proves this basic set clopen. Inside a component use the compact clopen image of a component clopen. These sets form a clopen basis of the actual carrier.

**Theorem 1.9 (Actual transverse convergence).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.transverse_tendsto_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.transverse_tendsto_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem transverse_tendsto_iff (ht : ∀ i, Continuous (t i))     (a : ℕ → I) (ha : Injective a) (z : ∀ n, P (a n)) (b : B) :     Tendsto (fun n => component t (a n) (z n)) atTop (𝓝 (core t b)) ↔       Tendsto (fun n => t (a n) (z n)) atTop (𝓝 b)

For an injective natural sequence of component indices and arbitrary chosen points in those components, convergence in the literal carrier to a core point is equivalent to Filter.Tendsto of their actual attachment images. Necessity uses collapse. Sufficiency uses convergence in the core together with eventual avoidance of every finite omitted set.

**Theorem 1.10 (A sequence from infinite actual multiplicity).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.sequence_of_infinite_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.sequence_of_infinite_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem sequence_of_infinite_multiplicity (ht : ∀ i, Continuous (t i))     (b : B) (hb : (multiplicity t b).Infinite) :     ∃ x : ℕ → Space t, Injective x ∧ Tendsto x atTop (𝓝 (core t b)) ∧       ∀ n, x n ≠ core t b

The set multiplicity(t,b) is the actual set of indices i for which b lies in range(t(i)). Embed the natural numbers in this infinite set and choose a point in each actual fibre. The resulting literal component points are injective, converge to the literal core point b, and never equal that limit.

**Theorem 1.11 (All convergent sequences in a sequence-free Hausdorff space).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.eventually_eq_of_no_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.eventually_eq_of_no_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem eventually_eq_of_no_sequence {X : Type*} [TopologicalSpace X] [T2Space X]     (hX : NoConvergentInjectiveSequence X) (x : ℕ → X) (b : X)     (hx : Tendsto x atTop (𝓝 b)) : ∀ᶠ n in atTop, x n = b

If the off-limit range is finite, its closed complement is a neighborhood of the limit and forces eventual equality. If infinite, enumerate distinct actual off-limit values and choose their original indices. These indices are injective and hence tend to infinity, yielding a convergent injective natural sequence, a contradiction.

**Theorem 1.12 (Full sequence-free characterization).**

Lean statement: `D5/S3/Topology/Resolution/RetractiveAttachment.no_sequence_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RetractiveAttachment.no_sequence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Supplied independent mathematical source and reviewer (2026). *Evolving continuous attachments and persistent compact range reservoirs*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Exact Lean signature, under the ambient parameters stated above: theorem no_sequence_iff [T2Space B] [∀ i, CompactSpace (P i)] [∀ i, T2Space (P i)]     (ht : ∀ i, Continuous (t i)) :     NoConvergentInjectiveSequence (Space t) ↔       NoConvergentInjectiveSequence B ∧ (∀ i, NoConvergentInjectiveSequence (P i)) ∧       ∀ b, (multiplicity t b).Finite

NoConvergentInjectiveSequence quantifies actual functions from the natural numbers, actual Function.Injective, and actual Filter.Tendsto to a neighborhood filter. The carrier has this property exactly when the core and every component have it and every actual core point has finite range multiplicity. For a component limit, the tail lies in its open embedded component. For a core limit, the collapse images eventually equal that point. Finite multiplicity and eventual avoidance of each fixed closed component leave no possible tail of an injective sequence. Empty index types are included. A limit occurring among the terms can occur at most once, and deleting that term gives the usual nontrivial-sequence convention.

## References

- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.compact_space`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.component_clopen_embedding`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.continuous_retraction`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.core_closed_embedding`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.eventually_eq_of_no_sequence`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.hausdorff`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.is_clopen_iff`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.is_open_iff`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.no_sequence_iff`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.sequence_of_infinite_multiplicity`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.transverse_tendsto_iff`
- Truth anchor: `D5/S3/Topology/Resolution/RetractiveAttachment.zero_dimensional`
