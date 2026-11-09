using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Separation;

internal sealed class AlexandroffDuplicateDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula Statement()
    {
        Formula k = F.Id("K");
        Formula d = Call("Duplicate", k);
        Formula projection = Call("Projection", k);
        Formula lower = Call("Lower", k);
        Formula upper = Call("Upper", k);
        Formula hypotheses = And(Call("CompactSpace", k), And(Call("TTwoSpace", k),
            And(Call("ConnectedSpace", k), Call("Nontrivial", k))));
        Formula locus = All("z", d, Iff(Call("HasClopenBasis", F.Id("z")),
            Call("Mem", F.Id("z"), Call("Range", upper))));
        Formula conclusion = And(Call("CompactSpace", d), And(Call("TTwoSpace", d),
            And(Call("Continuous", projection), And(Call("LeftInverse", projection, lower),
            And(Call("IsClosedEmbedding", lower), And(Call("Dense", Call("Range", upper)),
            And(locus, Call("Negation", Call("ZeroDimensionalSpace", d)))))))));
        return Disp(All("K", F.Id("TopologicalSpaceU"), Imp(hypotheses, conclusion)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Alexandroff duplicate has a dense clopen-basis locus and a closed connected bottom copy.",
        H("Alexandroff duplicate and its exact clopen locus"),
        Blocks(
            Paragraph(Text("K is an arbitrary compact Hausdorff connected nontrivial space with carrier in Type u. "
                + "Duplicate(K) has the actual carrier K times Bool. Lower(x) is (x,false), Upper(x) is (x,true), "
                + "and Projection(x,b) is x. Upper singletons are open. A bottom point Lower(x) in an open set U "
                + "has a base-open neighborhood V containing x such that Lower(y) belongs to U for every y in V, "
                + "and Upper(y) belongs to U for every y in V distinct from x. Thus the basic bottom neighborhoods "
                + "are exactly (V times Bool) minus the singleton Upper(x); this is not the product topology.")),
            Paragraph(Text("HasClopenBasis(z) means that for every actual ambient open U containing z there is an ambient "
                + "clopen C with z in C and C contained in U. TopologicalSpaceU bundles a carrier and its topology; "
                + "TTwoSpace means Hausdorff, Range denotes actual function range, and Negation is logical negation.")),
            Describe.Lean(
                DescribeId.Create("duplicate-topological-frontier"),
                DeclarationHandle.Create("D5/S3/Topology/Separation/AlexandroffDuplicate.topological_frontier"),
                H("Compact Hausdorff duplicate with exactly the upper clopen locus"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The duplicate is compact and Hausdorff. Projection is continuous and is a left inverse "
                        + "of Lower. Lower is a closed embedding of the original K. The range of Upper is dense. A point has "
                        + "a clopen neighborhood basis if and only if it belongs to that upper range. The duplicate is not zero-dimensional.")),
                    Paragraph(Text("For compactness, choose one bottom cover member and a base neighborhood at every base point. "
                        + "Finitely many such base neighborhoods cover K. Their duplicate neighborhoods miss at most the finitely many upper "
                        + "points with those chosen base coordinates; adding one cover member for each supplies a genuine finite subcover. "
                        + "This finite remainder is constructed, not assumed. For the clopen locus, the preimage of any clopen neighborhood "
                        + "under Lower is a nonempty clopen subset of the connected K, hence all of K. An open neighborhood omitting "
                        + "a different bottom point therefore has no such clopen refinement. The upper singleton supplies the converse.")),
                    Paragraph(Text("This is the topological prerequisite of proposition 34.2 in the matrix-bundle quantum source. "
                        + "Its two-sphere base is retained by specialization. The theorem does not construct the Hopf bundle, prove "
                        + "its endomorphism bundle nontrivial, establish winding or classify the original response D. Those are separate "
                        + "source clauses; no physical preparation or transport condition follows from this topology alone.")))))));
}
