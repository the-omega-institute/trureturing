using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class PronyTargetExtrapolationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite prefix controls later target moments without a node-separation assumption.",
        H("Separation-Free Prony Target Extrapolation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prony-target-amplification"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/PronyTargetExtrapolation.amplification"),
                H("The explicit amplification polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural d and n, C_d(n) is the sum of binom(n,k) times 2^k over "
                    + "0 <= k < d. The empty sum is zero. At fixed positive d this is a "
                    + "polynomial in n of degree d-1, with the usual binomial convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prony-separation-free-target-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/PronyTargetExtrapolation.prony_target_error_bound"),
                H("Uniform target recovery through colliding or vanishing modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f and g be actual finite exponential sums with d and e real "
                        + "nodes respectively, all in [-1,1]. Weights may be any real numbers, "
                        + "including zero, and repeated nodes are allowed. If epsilon is "
                        + "nonnegative and |f(k)-g(k)| <= epsilon for every 0 <= k < d+e, "
                        + "then |f(n)-g(n)| <= C_(d+e)(n) times epsilon for every natural n.")),
                    Paragraph(Text(
                        "The proof joins the two signed mode families, then removes one "
                        + "actual mode using f(n+1)-a f(n). This needs no division by node "
                        + "gaps. Induction on the remaining modes and on time yields the "
                        + "binomial amplification polynomial. The result controls target "
                        + "moments; it does not claim stable recovery of each spectral node "
                        + "or weight, an unknown mode bound, or a horizon-independent error."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction")),
        ]));
}
