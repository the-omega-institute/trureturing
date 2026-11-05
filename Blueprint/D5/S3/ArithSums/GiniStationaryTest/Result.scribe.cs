using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums.GiniStationaryTest;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/GiniStationaryTest/Result.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized stationary tests do not characterize Gini comparisons on the positive half-line.",
        H("Stationarity does not ensure comparison"), Blocks(
            Describe.Lean(DescribeId.Create("gini-stationary-counterexample-family"),
                DeclarationHandle.Create(Prefix + "counterexample_family"),
                H("A family in every dimension at least three"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n at least three, the parameters (r,s)=(1,0) and (p,q)=(2,-1) pass the normalized stationary test, while ((1,0),(2,-1)) is outside Gamma_n((0,infinity)). The stationary theorem applies to every positive normalized tuple and every multiplier satisfying the derivative equations. The tuple (1/2,1,...,1) reverses the required mean comparison. These statements refer to the same dimension and parameter pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gini-stationary-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the stationary characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The full claim is false. Specialize it to n=3, I=(0,infinity), and the pair ((1,0),(2,-1)). This interval is nonempty and order connected. Its quotient set is exactly the positive half-line: every quotient is positive, and every positive y is y/1. The infimum of that half-line is zero. The claimed equivalence would turn the stationary test supplied by the family theorem into universal mean comparison, contradicting the other conjunct of that same family theorem. The equal-parameter branch in the claim uses the exponential definition, although this refutation uses only unequal parameters. No assertion about a scaled parameter family is needed."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("grunwald-pales-2024-gini-stationary-test"),
                    ResolutionKind.Refuted)))));
}
