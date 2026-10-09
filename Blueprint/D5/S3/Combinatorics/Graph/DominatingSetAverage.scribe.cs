using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dominating sets have positive family sizes and exact rational average orders.",
        H("Finite dominating-set averages"),
        Blocks(
            Node("domsets", "Dominating sets", "domSets",
                "All subsets whose closed neighbourhood covers the vertex set.", DescribeRole.Definition),
            Node("avd", "Global average", "avd",
                "The sum of the cardinalities divided by the number of dominating sets.", DescribeRole.Definition),
            Node("avdat", "Local average", "avdAt",
                "The same mean restricted to sets containing a specified vertex.", DescribeRole.Definition),
            Node("starlike", "Star-like graphs", "StarLike",
                "Every vertex is a leaf or a stem with exactly one or two leaf neighbours. This is the definition in Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475.", DescribeRole.Definition),
            Node("avd-iso", "Isomorphism invariance", "avd_iso",
                "Mapping finite sets along a graph isomorphism gives a cardinality-preserving bijection of the dominating families.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
