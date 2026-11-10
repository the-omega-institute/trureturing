using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class MeanSquareCorrelationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean-square raw correlation errors yield total absolute error estimates.",
        H("Mean-square prime correlations"),
        Blocks(
            Paragraph(Text(
                "Chan, A note on primes in short intervals, International Journal of Number Theory "
                + "2 (2006), 105–110, DOI 10.1142/S1793042106000437, supplies the mean-square weakening for single-interval moments. "
                + "The finite-set formulation here is used for overlapping mixed moments. "
                + "Only cutoffs between N and 2N occur in the hypothesis.")),
            Describe.Lean(
                DescribeId.Create("correlation-error"),
                DeclarationHandle.Create(Prefix + "correlationError"),
                H("Raw finite-set correlation error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real-valued function SS on finite natural shift sets, a real cutoff y "
                    + "and a finite set D, the raw error is the sum over positive integers n at most "
                    + "floor y of the product of von Mangoldt(n+d) for d in D, minus y SS(D)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-square-hl-order"),
                DeclarationHandle.Create(Prefix + "MeanSquareHL"),
                H("Mean-square hypothesis through a prescribed order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural maximal order q, MeanSquareHL(q,SS,beta) requires the uniform "
                    + "mean-square raw error bound C N^(1+2 epsilon) K^r for every order 1<=r<=q. "
                    + "For each epsilon>0 and M>=1, one positive C and one threshold work for all "
                    + "such r, natural 1<=K<=M N^beta and real N<=y<=2N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-square-hl-four"),
                DeclarationHandle.Create(Prefix + "MeanSquareHL4"),
                H("The four-point mean-square instance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive epsilon and each real M at least one, there are a positive "
                    + "C and a real threshold N0 such that, for every real N at least N0, every "
                    + "integer order r from one through four, every natural K with 1<=K<=M N^beta, "
                    + "and every real y with N<=y<=2N, the sum of squared absolute raw errors over "
                    + "all injective ordered r-tuples in {1,...,K} is at most C N^(1+2 epsilon) K^r. "
                    + "The raw error is exactly the ordered correlation error in HL4."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-square-correlation-l-one"),
                DeclarationHandle.Create(Prefix + "meanSquare_correlation_l1"),
                H("Absolute errors over unordered shift sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MeanSquareHL(q,SS,beta). For every positive epsilon and M>=1 "
                    + "there is A>=0 such that, for all sufficiently large real N>=2, all r from "
                    + "one through q, all natural 1<=K<=M N^beta, and N<=y<=2N, the sum of "
                    + "absolute correlationError(SS,y,D) over all r-element subsets D of {1,...,K} "
                    + "is at most A N^(1/2+epsilon) K^r. Every such subset has an injective "
                    + "enumeration. Cauchy–Schwarz and the bound K^r on their number supply the estimate."))),
                DescribeRole.Theorem))));
}
