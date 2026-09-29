using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Catalan-weighted recurrence implies the cubic equation for the ordinary generating series.",
        H("From the Recurrence to the Cubic"),
        Blocks(Node("arrow-thirty-two-cubic-recurrence", "The cubic from a Catalan recurrence",
            "cubic_of_recurrence",
            "Let a be a sequence of natural numbers with a at zero equal to one. If each positive term is its predecessor plus the Catalan-weighted sum of coefficients of powers of its generating series, then that series F satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0.",
            DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
