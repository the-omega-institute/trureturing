using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ArithmeticRamsey;

internal sealed class RadoLastExceptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/hughes2026radolastexception");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-colour Rado lower bound is exact above the explicit last exception for every k at least three.",
        H("The all-parameter Rado last-exception theorem"),
        Blocks(
            Node("exception-good", "Good colourings for the reflected equation", "Good",
                "Good records the absence of a monochromatic solution of x + y = k z + b in a finite interval and supplies the forcing and reflection mechanism.", DescribeRole.Definition),
            Node("exception-forced", "Forced and IsRado", "Forced",
                "Forced quantifies over every colouring of a finite interval, while IsRado adds minimality of the endpoint.", DescribeRole.Definition),
            Node("exception-valid", "The parity validity condition", "Valid",
                "A parameter is valid when k is odd or c is even, matching the parity range of the theorem.", DescribeRole.Definition),
            Node("exception-rado-eq", "Exact Rado number above the boundary", "rado_eq_LB",
                "For every k at least three and every valid c greater than cstar(k), the Rado number is exactly LB(c,k). The lower-bound and reflected upper-bound arguments both contribute.", DescribeRole.Theorem),
            Node("exception-boundary", "Boundary non-forcing", "not_forced_cstar",
                "At cstar(k), the explicit boundary colouring prevents forcing on [1,LB(cstar(k),k)]. This is a non-forcing statement and does not assert that a finite boundary Rado number exists.", DescribeRole.Theorem),
            Node("exception-valid-cstar", "Validity of the boundary parameter", "valid_cstar",
                "The piecewise cstar(k) satisfies the validity parity condition for every k at least three.", DescribeRole.Theorem),
            Node("exception-complete", "Expanded two-halves theorem", "rado_last_exception",
                "For every k at least three, every valid c above cstar(k) forces at LB(c,k) and admits a lower-interval avoiding colouring, while cstar(k) admits the explicit avoiding boundary colouring.", DescribeRole.Theorem),
            Node("exception-rado-form", "IsRado formulation", "rado_last_exception_rado",
                "The same result is stated with IsRado: all valid parameters above cstar(k) have the lower-bound Rado number, and any finite boundary Rado number lies strictly above the lower bound.", DescribeRole.Theorem),
            Node("exception-threshold", "Threshold characterization", "nu_iff",
                "For every k at least three, a cutoff v has the exact lower-bound property for all valid c at least v exactly when v exceeds cstar(k).", DescribeRole.Theorem))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
