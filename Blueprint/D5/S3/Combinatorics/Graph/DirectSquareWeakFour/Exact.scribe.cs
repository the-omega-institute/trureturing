using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourExactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weak-four metric dimension of complete graph direct squares", H("Exact weak-four metric dimension of complete graph direct squares"),
        Blocks(
            Paragraph(Text("Farhan, Kuziak and Yero, arXiv:2605.22307v1, Section 3 paragraph S3.p17.1 and Section 6 first bullet ask for this value for every n at least four. Adjacency changes both coordinates. Weak resolution quantifies over distinct pairs, as explicitly stated in Proposition 2.2. The finite feasible family has an attained minimum.")),
            Node("lower-bound", "Universal landmark lower bound", "lower_bound",
                "For every n at least four, every actual weak-four landmark set has at least target n elements. Sets at or above 3n minus 2 already exceed the target. Smaller sets have incidence minimum degree two, so the linear lower bound gives the ceiling term. At order five, the eleven-element equality possibility is excluded.", DescribeRole.Theorem),
            Node("minimum", "Nonempty feasible family and attainment", "minimum",
                "For every n at least four there exists a weak-four landmark set with cardinality target n, and its cardinality is no larger than that of every weak-four landmark set.", DescribeRole.Theorem),
            Node("claim", "The exact original formula", "claim",
                "For every natural n at least four, the actual weak-four dimension is 2n plus the ceiling of 2n over eleven, plus one exactly when n equals five. Natural division of 2n plus 10 by eleven represents the ceiling.", DescribeRole.Definition),
            Node("result", "Exact weak-four dimension", "result",
                "The formula holds at every n at least four. The construction gives nonemptiness and an attained feasible cardinality, while the universal lower bound applies to every feasible cardinality. Therefore the natural infimum is the true least cardinality. In particular the value at order nine is twenty; the upper bound twenty-one from source Theorem 3.3 is not always sharp.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("farhan-kuziak-yero-2026-direct-square-weak-four"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
