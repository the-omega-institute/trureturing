using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class KarttunenA401714Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/KarttunenA401714.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/karttunen2026a401714");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A radical quotient below the least missing prime forces the joint divisor-sum inequality.",
        H("The radical quotient and two divisor sums"),
        Blocks(
            Paragraph(Text(
                "For a positive integer N, let rad(N) be the product of its distinct "
                + "prime divisors. Let U(N) be the sum of its positive unitary divisors, "
                + "and S(N) the sum of its positive squarefree divisors; both include one. "
                + "The reciprocal conjecture lines in the two source entries express "
                + "one implication, recorded in the linked problem dossier.")),
            Describe.Lean(
                DescribeId.Create("karttunen-a401714-least-missing-prime"),
                DeclarationHandle.Create(Prefix + "leastMissingPrime"),
                H("The least missing prime"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The least missing prime is the smallest prime that does not divide N. "
                    + "The frozen least-missing-prime threshold theorem supplies existence. "
                    + "Nat.find selects the least witness to primality and nondivisibility."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("karttunen-a401714-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The divisor-sum implication"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For every positive integer N, if N/rad(N) is less than its least "
                    + "missing prime, then U(N)+S(N) is at least 2N. The strict inequality "
                    + "forces every prime at most N/rad(N) to divide N. The mandatory "
                    + "support theorem then gives the claimed inequality. No bound on "
                    + "N, parity restriction or restriction on its number of prime "
                    + "divisors is imposed."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a401714-unitary-squarefree-divisor-sum"),
                    ResolutionKind.Proved)))));
}
