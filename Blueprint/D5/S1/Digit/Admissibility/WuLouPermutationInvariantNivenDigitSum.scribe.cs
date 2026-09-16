using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class WuLouPermutationInvariantNivenDigitSumDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/wu2025pinn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu and Lou's permutation-invariant decimal Niven digit-sum bound.",
        H("Permutation-Invariant Niven Digit-Sum Bound"),
        Blocks(
            Paragraph(Text(
                "DecimalPINN is the source-faithful object: a nonempty list of decimal digits "
                + "whose digit sum divides the Nat.ofDigits value of every list permutation.")),
            Node(
                "DecimalPINN",
                "Permutation-invariant decimal Niven number",
                "The structure records a nonempty decimal digit list, its nonzero leading digit, "
                    + "the bound that every digit is below ten, and divisibility of every "
                    + "permuted Nat.ofDigits value by the source digit sum.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node(
                "result",
                "Distinct-digit digit-sum bound",
                "For at least two nonzero digit occurrences and at least two distinct digit "
                    + "values, the digit sum is divisible by three, is at least three, and is "
                    + "at most 81. The divisibility-by-three clause is literature-attested by "
                    + "Wu and Lou's Theorem 1 consequence in section 8.4; the lower bound follows "
                    + "from positivity; the upper bound is the repository-derived settlement of "
                    + "the conjectural bound. The formal proof reuses the source object's "
                    + "permutation-divisibility field and arithmetic normalization.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wu-lou-permutation-invariant-niven-digit-sum-bound"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string declaration,
        string title,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("wu-lou-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration),
        H(title),
        StatementSource.WithoutFormula(),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role,
        claim);
}
