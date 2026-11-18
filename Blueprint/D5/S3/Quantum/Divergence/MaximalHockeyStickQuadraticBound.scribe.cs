using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for every actual finite quadratic reverse test",
        H("A lower bound for every actual finite quadratic reverse test"), Blocks(
            Paragraph(Text("The lower bound proves known quadratic optimality in the exact singular finite preparation model used here. Canonical spectral and operator-convex optimality are credited to Hiai as antecedents; no arbitrary general-convex attainment is inferred.")),
            Node("quadraticValue", "For S=A+B and T=normalize S (A-B), quadraticValue A B is Re Tr(S T^2). The generalized inverse support keeps singular and zero pairs in scope.", false, false),
            Node("quadratic_value_le_test", "For any PSD A,B and any actual finite ReverseTest, quadraticValue A B <= starCost R. The proof normalizes the actual state components, handles zero total label masses, and applies the subunital square inequality.", true, false),
            Node("quadratic_value_le_maximal", "For PSD A,B, the EReal embedding of quadraticValue is a lower bound for the infimum over all actual finite quadratic tests. QuadraticCanonical combines it with a spectral witness to identify the true infimum.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-quadratic-bound-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
