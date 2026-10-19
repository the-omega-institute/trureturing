using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality-size constructions at every order", H("Equality-size constructions at every order"),
        Blocks(
            Paragraph(Text("The finite base sets are explicit coordinate lists. Their degree, path and rectangle properties are checked by kernel reduction. An induction adjoining an eleven-by-eleven block proves the unrestricted construction; no finite range is extrapolated.")),
            Node("target", "Exact cardinality expression", "target",
                "For every natural n, target n is 2n plus natural division of 2n plus 10 by eleven, with one extra landmark exactly at n equal to five. The division term is the ceiling of 2n over eleven.", DescribeRole.Definition),
            Node("all-design", "Every incidence size", "all_design",
                "For every n at least four there is a Good incidence set with exactly target n edges. Explicit base designs cover orders four through sixteen. For every larger order remove eleven, use the smaller design, adjoin the twenty-four-edge order-eleven block, and relabel both parts. The natural ceiling increases by exactly two.", DescribeRole.Theorem),
            Node("construction", "Actual equality-size landmark sets", "construction",
                "For every n at least four a finite set of actual direct-product vertices is weak four-resolving and has cardinality exactly target n.", DescribeRole.Theorem),
            Node("target-lt-three", "Strict low-degree threshold", "target_lt_three",
                "For every n at least four the target is strictly less than 3n minus 2. This makes the minimum-degree-two reduction available whenever a set could beat the construction.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
