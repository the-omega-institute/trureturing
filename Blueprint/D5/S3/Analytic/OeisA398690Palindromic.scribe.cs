using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OeisA398690PalindromicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OeisA398690Palindromic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/chapoton2026a398690");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every simplified Verlinde row has a palindromic numerator of its expected degree.",
        H("Palindromic Numerators of OEIS A398690"),
        Blocks(
            Paragraph(Text(
                "For natural r and q, the source function is the real signed sine sum "
                + "A(r,q)=(2q+1)^(-1) sum from j=0 to 2q of (-1)^(rj) "
                + "sin((2j+1)pi/(4q+2))^(2-r). The exponent is an integer exponent. "
                + "The conjectured rows use r=n+3, so r is at least three.")),
            Describe.Lean(
                DescribeId.Create("a398690-source"),
                DeclarationHandle.Create(Prefix + "simplifiedVerlinde"),
                H("Simplified Verlinde source sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the A398690 comment's signed finite sum. Its angle "
                    + "2pi/(8q+4) simplifies to pi/(4q+2). The real power uses "
                    + "the same integer exponent 2-r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a398690-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("All row numerators are palindromic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n there is a real polynomial R of degree "
                    + "exactly n such that its formal power series equals "
                    + "(1-z)^(n+1) times the series whose coefficient at q is "
                    + "A(n+3,q). For every j at most n, the coefficients of R "
                    + "at j and n-j are equal. Chebyshev node moments identify "
                    + "every source coefficient with a polynomial model; the "
                    + "model's reflection gives numerator reciprocity."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a398690-palindromic"),
                    ResolutionKind.Proved)))));
}
