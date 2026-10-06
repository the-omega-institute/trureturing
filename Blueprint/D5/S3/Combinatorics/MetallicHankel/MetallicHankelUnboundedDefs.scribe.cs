using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive metallic parameter, each shifted Hankel determinant sequence at shifts at least n+3 is unbounded in absolute value.",
        H("The Large-Shift Metallic Hankel Conjecture"),
        Blocks(
            Node("metallic-hankel-unbounded-defs-claim", "Unboundedness at every large shift", "claim",
                "For every integer n at least one, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi, every integer ell at least n+3 and every nonnegative integer M, there is a nonnegative integer j such that the absolute value of Delta_j^{(ell)} exceeds M. Here Delta_j^{(ell)} is the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, with row and column indices starting at zero and empty determinant one. This is part 2 of Conjecture E of Han and Pedon, with ell as the varying shift.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
