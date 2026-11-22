using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class MobiusCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Möbius truncation of the Chebyshev root sum",
        H("The arithmetic error and its integrated bound"),
        Blocks(
            Paragraph(Text("A pointwise bound on the signed truncation by C x^(1/(m+1)) transfers to the normalized integral with coefficient C/(1−1/(m+1)). The identity uses the actual difference of prime-only and complete tails and is valid for every cutoff x≥2.")),
            Entry("chebyshev-mobius-truncation", "chebyshev_mobius_truncation",
                "A geometric bound uniform in the truncation order",
                "For t ≥ 2 and an integer m ≥ 2, approximate θ(t) − ψ(t) by the finite sum "
                + "of μ(n)ψ(t^(1/n)) over 2 ≤ n ≤ m. The absolute error is at most "
                + "2(log 4 + 4)(1 + (m + 1)/log 2)t^(1/(m+1)). "
                + "Finite Möbius inversion cancels the divisor multiplicities at a common cutoff. "
                + "A root term of degree n vanishes below t = 2^n, and above that threshold "
                + "the global bound for ψ gives a geometric bound in n."),
            Entry("integrated-mobius-truncation", "integrated_mobius_truncation",
                "The normalized prime-only tail",
                "For x ≥ 2 and m ≥ 2, subtract the complete Chebyshev tail and the sum of "
                + "the μ(n)-weighted root integrals from the prime-only tail. Each root integral "
                + "uses the kernel ψ(t^(1/n))/t² on (x,∞). The absolute residual after multiplication "
                + "by sqrt(x) is at most 2(log 4 + 4)(1 + (m + 1)/log 2) times "
                + "x^(1/(m+1) − 1/2) divided by 1 − 1/(m+1)."))));

    private static DocumentBlock Entry(string id, string name, string heading, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
