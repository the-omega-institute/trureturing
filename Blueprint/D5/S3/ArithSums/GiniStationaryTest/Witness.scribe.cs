using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums.GiniStationaryTest;

internal sealed class WitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/GiniStationaryTest/Witness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of strict Gini comparison reversals on the positive half-line.",
        H("One small coordinate"), Blocks(
            Describe.Lean(DescribeId.Create("gini-stationary-witness-identity"),
                DeclarationHandle.Create(Prefix + "witness_identity"),
                H("Factorization of the comparison numerator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all real t and k, (t+k)^3(1+kt) - (k+1)^3 t(t^2+k) equals k(t-1)^3(t-k^2). The identity is polynomial and has no positivity assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gini-stationary-tuple-power-sum"),
                DeclarationHandle.Create(Prefix + "sum_highTuple_rpow"),
                H("Power sum of the comparison tuple"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural m and real t and p, the sum of the p-th powers of the tuple (t,1,...,1) with m+1 coordinates is t^p+m. Splitting off the first coordinate gives the formula used at exponents 1, 0, 2 and -1 in the strict comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gini-stationary-strict-witness"),
                DeclarationHandle.Create(Prefix + "witness_comparison"),
                H("Strict reversal in every dimension at least three"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n at least three and every real t with 0<t<1, the tuple x=(t,1,...,1) satisfies G_{2,-1}(x)<G_{1,0}(x). Put k=n-1. The arithmetic mean is (t+k)/(k+1), and the cube of G_{2,-1}(x) is t(t^2+k)/(1+kt). The factorization has positive right side: k is positive and both (t-1)^3 and t-k^2 are negative. Positive denominators and monotonicity of the real cube root give the strict comparison. The tuple and the unequal-parameter Gini expression are reused from the endpoint comparison module."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gini-stationary-not-gamma"),
                DeclarationHandle.Create(Prefix + "not_mem_Gamma"),
                H("Failure of universal comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n at least three, the parameter pair ((1,0),(2,-1)) does not belong to Gamma_n((0,infinity)). The preceding strict comparison at t=1/2 contradicts the defining comparison at every positive tuple."))),
                DescribeRole.Theorem))));
}
