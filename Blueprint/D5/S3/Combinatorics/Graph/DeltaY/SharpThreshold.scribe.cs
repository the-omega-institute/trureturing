using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeltaY;

internal sealed class SharpThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.";
    private static readonly LibraryNoteRef Zhou =
        LibraryNoteRef.Create("D5/L/Rewriting/zhou2026deltay");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six is the least minimum-degree threshold at which ordinary and strong reachability agree up to graph isomorphism.",
        H("Zhou's sharp degree-six threshold"),
        Blocks(
            Describe.Lean(DescribeId.Create("delta-y-threshold-predicate"),
                DeclarationHandle.Create(Prefix + "P"), H("Equality of reachable families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Zhou),
                Blocks(Paragraph(Text("P(d) says that for every finite simple graph with every vertex of degree at least d, ordinary and strong finite histories reach the same family of graphs up to isomorphism."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("delta-y-sharp-threshold"),
                DeclarationHandle.Create(Prefix + "zhou_sharp_threshold"), H("The exact threshold"),
                StatementSource.FromAuthor(Threshold()), AssessedProvenance.FromRepo(Zhou),
                Blocks(
                    Paragraph(Text("The two-color invariant makes every reachable reverse move strong when the starting graph has minimum degree at least six.")),
                    Paragraph(Text("Start with the complete graph on 0 through 6 and remove the pairs 06 and 14. Perform forward moves on 012 at 7 and 034 at 8, reverse at 0, perform a forward move on 157 at 9, then reverse at 1.")),
                    Paragraph(Text("The last center has neighbors 3, 6 and 9, with just the pair 36 already present. Its removal lowers the edge count from 19 to 18. Strong histories and graph isomorphisms preserve edge count, so the endpoint separates the two reachable families at every threshold below six."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Threshold()
    {
        var d = F.Id("d");
        var six = D(6);
        var below = new Formula.Relation(d, FormulaRelationOperator.LessThan, six);
        var fails = new Formula.Logic(below, FormulaLogicOperator.Implies, new Formula.Not(P(d)));
        var all = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"), F.Id("Nat"), fails);
        return Disp(new Formula.Logic(P(six), FormulaLogicOperator.And, Seq(Open, all, Close)));
    }

    private static Formula P(Formula degree) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("P"), [degree]);
}
