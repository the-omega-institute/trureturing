using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.MaskedCycles;
internal sealed class StabilizerMaskedCycleRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual character mask and generated root field give a rank correction of zero or two on every even-cycle component.",
        H("Stabilizer Even-Cycle Rank Correction"), Blocks(
            Paragraph(Text("The original source family has odd n>=3, q>=2, any finite vertex type V (in particular Fin(N)), every symmetric zero-diagonal Gamma over F2, any coloring col:V->Fin(q) including empty parties, every character t:Fin(q-1)->ZMod(n), and every primitive nth root zeta in the algebraic closure of F2. RootField(zeta) is literally IntermediateField.adjoin F2 {zeta}. The proof only needs n nonzero and the given primitive-root property, so it retains the complete original family.")),
            Paragraph(Text("The translation delta(c)(i) is one when i=c and zero otherwise; the last party has the zero translation. The actual character readout is the dot product f_t(c)=sum_i t(i)delta(c)(i). partyPartition is its kernel equivalence relation. fibrePartition consists of its nonempty equivalence classes with the partition law. The mask is assigned piecewise: mask(Gamma,col,t)(u,v)=0 when the two colors lie in one actual fibre block, and otherwise it equals Gamma(u,v). A zero mask entry can also come from a different-block nonedge with Gamma(u,v)=0, so the zero value is not equivalent to common-block membership. The proof establishes that common-block membership is equivalent to equality of the original character readouts.")),
            Paragraph(Text("lambda(u)=zeta^f_t(col(u)), Lambda is its actual diagonal matrix, and M=Lambda Gamma+Gamma Lambda over the generated field. Primitive-root power injection proves lambda(u)=lambda(v) exactly when the character readouts agree. In characteristic two, the actual matrix entry is Gamma(u,v)(lambda(u)+lambda(v)); it is nonzero exactly on the actual masked graph. Because Gamma is F2-valued, every edge has Gamma(u,v)=1 and weight lambda(u)+lambda(v). edgeWeight bundles this nonzero value as a unit on edges; its default off the support is never traversed.")),
            Describe.Lean(DescribeId.Create("component-rank-difference-alpha"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/MaskedCycles/StabilizerMaskedCycleRank.component_rank_difference_alpha"),
                H("The Actual Same-Component Correction"),
                StatementSource.FromAuthor(Disp(All("data", Call("OriginalStabilizerData"),
                    All("C", Call("ConnectedComponent", Call("maskedGraph", F.Id("data"))),
                    All("k", Call("Nat"), All("z", Call("GraphIso", Call("cycleGraph", Call("mul", D(2), Call("add", F.Id("k"), D(2)))), Call("ComponentGraph", F.Id("C"))),
                    And(Call("IsCycle", Call("componentCircuit", F.Id("data"), F.Id("C"), F.Id("z"))),
                    And(Eq(Call("length", Call("componentCircuit", F.Id("data"), F.Id("C"), F.Id("z"))),
                        Call("mul", D(2), Call("add", F.Id("k"), D(2)))),
                    Eq(Call("IntRankDifference", Call("MRestricted", F.Id("data"), F.Id("C")), Call("MaskRestricted", F.Id("data"), F.Id("C"))),
                        Call("If", Eq(Call("alpha", Call("edgeWeight", F.Id("data")), Call("componentCircuit", F.Id("data"), F.Id("C"), F.Id("z"))), D(1)), D(0), D(2))))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("C is an actual connected component of the actual masked graph, and z is any graph isomorphism from the ordinary cycle on L=2(k+2) vertices to C's induced graph. Thus every even length L>=4 and arbitrary cyclic labeling are retained. The parity isomorphism constructs the two alternating classes in this same component. componentCircuit is mapped through z and then through the actual component inclusion into the original masked graph. The theorem certifies that this is a simple cycle of length L.")),
                    Paragraph(Text("Both principal matrices are restricted by the same subtype inclusion C->V. Their symmetry, exact support, and actual edge-entry correspondences are proved from the original data. The weighted restriction uses rank_even_cycle over RootField(zeta). The actual masked restriction is proved equal to the actual adjacency matrix of C's induced graph; rank_even_adjacency applies directly over F2. These two applications avoid any assumed extension-of-scalars bridge. All F2 edge entries are one, so the two adjacency matching products are both one and that actual masked restriction has rank L-2. The weighted restriction has rank L-2 or L according to equality of its actual matching products. This includes the ordinary F2 even-cycle adjacency specialization.")),
                    Paragraph(Text("The public circuit_alpha computation is applied to the actual stabilizer edge units after the graph maps. Coercing the two unit products proves, without a supplied bridge, that the actual alpha equals one exactly when the two products of lambda(u)+lambda(v) agree. Subtracting the two actual ranks in the integers gives delta_C(t)=0 for alpha=1 and delta_C(t)=2 for alpha!=1. This is a conditional theorem of the stated graph-state model; it asserts no additional empirical premise. Weighted paths and odd cycles are handled by WeightedPathCycleRank and retain every nonzero characteristic-two edge weight."))),
                DescribeRole.Theorem),
            Paragraph(Text("The matrix-rank formulas with unit weights are established graph-theoretic results. The proof reuses NoEvenCycleRank.rank_eq_twice_maximum_matching for paths and odd cycles, the pinned rank and finite-dimensional APIs, and WeightedVertexProducts.alpha. Its new all-length inference is the cyclic transport kernel calculation in WeightedCycleKernel, followed by the actual support, reindexing and product correspondence above. No claim of literature novelty follows from a library search.")))));
    private static Formula Call(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open,a,Close), FormulaLogicOperator.And, Seq(Open,b,Close));
}
