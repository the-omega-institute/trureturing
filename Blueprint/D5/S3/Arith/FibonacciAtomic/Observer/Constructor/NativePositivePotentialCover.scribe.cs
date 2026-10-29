using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativePositivePotentialCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed source cycles and minimum natural block bases",
        H("The total named source family"), Blocks(
            Paragraph(Text("Let p present the entire finite set X of declared names, B be a finite list of selected BranchEquation cases, and S be the actual successful free-shape unifier of shapeEquations(B). The assignment s=action(p,S) retains every named term, including unused names. A residual occurrence records its name, its ordered address and its residual sort. The list occurrenceVertices(p,s) includes isolated occurrences. An occurring sort j has at least one such vertex. Decidable equality on X serves only to select that finite sort.")),
            Entry("sortEdges", "The actual sort edges",
                "sortEdges(B,s,j) filters sourceOffsetEdges(B,s) by the sort of the left endpoint. It preserves list order, every repeated equation and every parallel edge. For a successful unifier, both endpoints are actual vertices of the same sort. A source shift contributes its original nonnegative integer offset. Ordinary and equality comparisons contribute zero. The primitive constraints r=r'+d and r=d, the natural collapse parameter r and its ranks r,r+1,r+2 remain in the original branch data; this block theorem does not solve those scalar constraints."),
            Entry("signedGraph", "Both orientations retain each edge identity",
                "For each indexed sort edge U=V+d, signedGraph has a forward edge from V to U and a reverse edge from U to V. The Boolean orientation is part of the edge identity. Thus zero offsets, repeated edges and parallel edges remain explicit, and reversing an edge changes only its orientation and weight."),
            Entry("signedWeight", "The signed offset",
                "The forward weight is d and the reverse weight is -d. A walk has the sum of its oriented edge weights. For a potential delta satisfying every original edge, the sum is delta(finish)-delta(start), so two paths with the same endpoints have the same sum."),
            Entry("ZeroCycles", "Zero signed sum on every closed walk",
                "ZeroCycles asserts that every closed walk at every occurrence has weight zero. The condition refers to the actual sort edge list rather than an epoch or head-power graph. Vertices without incident edges contribute only empty walks."),
            Entry("Potential", "Integer differences on the source edges",
                "Potential(B,s,j,delta) states delta(U)=delta(V)+d for every edge U=V+d of the selected sort. Pairing both orientations identifies this exact equality with the inequalities of Maths.MaxPlusPotential.IsPotential. The finite supplier theorem exists_isPotential_iff_forall_closedWalk_nonpos supplies an integer potential when all signed cycles vanish; its statement and proof are used directly."),
            Entry("BlockSolution", "Natural ranks on an arbitrary leaf carrier",
                "A block valuation u assigns a natural rank u(U,l) to each occurrence U and each leaf l. BlockSolution imposes the original signed integer equation at every leaf and every selected edge. The carrier L may be any type; no cardinality bound is imposed. Detecting inconsistency requires L to be nonempty. In particular this includes every nonempty finite ground-shape leaf set."),
            Describe.Lean(DescribeId.Create("source-sort-minimum-natural-base"),
                DeclarationHandle.Create(Prefix + "source_sort_minimum_base"),
                H("Minimum-potential normalization classifies every natural block solution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every p,B,S,j as above with at least one occurrence of j, the theorem has two conclusions. If ZeroCycles fails, then for every nonempty type L and every natural block valuation u on L, BlockSolution fails. If ZeroCycles holds, there exist one integer potential delta, one actual vertex b of sort j, and natural offsets a(U), independent of L and u. The chosen b minimizes delta among all actual vertices of sort j, a(b)=0, and a(U)=delta(U)-delta(b) as an integer at every such vertex. For every L, including the empty type, and every u, BlockSolution holds exactly when u(U,l)=u(b,l)+a(U) for every actual vertex U of sort j and every l. Consequently every natural base function gives a solution by that formula, with arbitrary values outside the selected sort.")),
                    Paragraph(Text("A nonempty leaf valuation at any fixed leaf gives an integer potential, which telescopes around closed walks and excludes nonzero cycle sums. Conversely the paired-edge supplier gives a potential when cycles vanish. Connectivity of the actual MGU source graph identifies all vertices of the same residual sort. Subtracting any two edge potentials gives a constant along this equivalence closure. Choosing a minimum on the finite vertex list makes every potential difference nonnegative; exact integer-to-natural conversion then gives the natural rank classification. The reverse implication uses the actual endpoints of every source edge and the same potential equation. This argument includes isolated unused names, empty branch lists, zero offsets, repeated and parallel constraints. If no sort occurs, the theorem is unnecessary and there is no block-base factor.")),
                    Paragraph(Text("This theorem establishes the signed-cycle and natural-rank portion of the one-base result. It does not produce an executable potential-search program or extract block valuations and their actual subtree identities from an original canonical branch valuation. With those concrete identities given, the following result proves normality and exact native recovery. Constructing those identities from the original branch equations remains a separate obligation. No finite positive image-cover theorem or signed pullback follows merely from this rank classification."))), DescribeRole.Theorem)
            ,Entry("Leaves", "Nonempty finite leaves of an ordered shape",
                "The leaves of a primitive shape form Unit; leaves of a pair form the disjoint sum of the two child leaf sets. These types are finite and nonempty. Distinct positions remain distinct even when their ranks are equal."),
            Entry("fill", "Fill the same ground shape with natural ranks",
                "fill(T,r) puts rank r(l) at each ordered leaf l of T. Adding a natural number a to every rank gives exactly shiftCode(a,fill(T,r)). This is a structural property of finite ordered codes, with no normality assumption."),
            Describe.Lean(DescribeId.Create("source-canonical-block-recovery"),
                DeclarationHandle.Create(Prefix + "source_canonical_block_recovery"),
                H("Recover normal occurrence blocks by the actual native shifts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every actual successful source unifier and occurring sort with zero signed cycle sums, there are one actual base vertex b and natural offsets a with a(b)=0, independent of all ground fillings. Let T be any finite ground shape, u a natural rank valuation on its nonempty leaf type satisfying BlockSolution, and C the entire family of normal named codes. Suppose that at every actual occurrence v of this sort, the subtree of C(v.name) at v.address is exactly fill(T,u(v)). Then fill(T,u(b)) is normal. For every actual v of the sort, fill(T,u(v)) equals shiftCode(a(v),fill(T,u(b))); its expansion is the actual native substitution iterated a(v) times on the expansion of the base; and rankInverse(a(v),u(v,l)) is exactly some(u(b,l)) at every leaf.")),
                    Paragraph(Text("The rank classification supplies the same minimum vertex for all fillings. Normality descends along the actual ordered subtree address in the normal named code. Structural filling converts the pointwise rank equation to literal code translation. NativeFiniteNormalInversion.shift_expand gives the native equality, and exact_natural_rank_inverse gives every exact inverse rank without truncated subtraction. No desired normal base, integer potential or reconstruction equality is assumed. The concrete subtree identities and the source BlockSolution remain hypotheses: deriving them automatically from a full canonical valuation of BranchEquation.Holds is not asserted here."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("source-potential-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
