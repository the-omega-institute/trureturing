using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthMSDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Single-length prime moments and their correlation hypotheses.",
        H("Single-length prime moments"),
        Blocks(
            Paragraph(Text(
                "Let E(x)=psi(x)-x and D(v,x)=E(x+v)-E(x). The discrete moment sums "
                + "D(K,n)^k over 1<=n<=N. The main term has coefficient one for k=2 "
                + "and three for k=4, and integrates (log(y/v)+B)^(k/2), where "
                + "B=1-gamma-log(2*pi). MS20 gives the correlation error bound on "
                + "a specified family of integer lengths. MSThirdTheorem is an explicit "
                + "hypothesis giving Montgomery–Soundararajan's second and fourth moment "
                + "estimates, with first error exponents -1/16 and -1/32 respectively.")),
            Describe.Lean(
                DescribeId.Create("chebyshev-error"),
                DeclarationHandle.Create(Prefix + "chebyshevError"),
                H("Chebyshev error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complete Chebyshev error is E(x)=psi(x)-x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-increment"),
                DeclarationHandle.Create(Prefix + "primeIncrement"),
                H("Prime increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The centered prime increment of length v at x is E(x+v)-E(x), where E=psi-id."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("montgomery-soundararajan-constant"),
                DeclarationHandle.Create(Prefix + "montgomerySoundararajanConstant"),
                H("Montgomery soundararajan constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithmic constant B is one minus the Euler–Mascheroni constant minus log(2 pi)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discrete-prime-moment"),
                DeclarationHandle.Create(Prefix + "discretePrimeMoment"),
                H("Discrete prime moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The discrete moment of order k at integer cutoff N and length K is the sum of the kth powers of E(n+K)-E(n) over 1<=n<=N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continuous-prime-moment"),
                DeclarationHandle.Create(Prefix + "continuousPrimeMoment"),
                H("Continuous prime moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The continuous moment of order k is the integral of (E(x+v)-E(x))^k from one to Y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("montgomery-soundararajan-main-term"),
                DeclarationHandle.Create(Prefix + "montgomerySoundararajanMainTerm"),
                H("Montgomery soundararajan main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k=2 or k=4, the main term is mu_k v^(k/2) times the integral of (log(y/v)+B)^(k/2) from one to Y, with mu_2=1 and mu_4=3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("montgomery-soundararajan-error"),
                DeclarationHandle.Create(Prefix + "montgomerySoundararajanError"),
                H("Montgomery soundararajan error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The error envelope is Y (log Y)^(k/2) v^(k/2) (v/log Y)^(-1/(8k)) plus v^k Y^(1/2+epsilon)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ms20"),
                DeclarationHandle.Create(Prefix + "MS20"),
                H("Ms20"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equation (20) bounds the correlation error for every order from one through k, every tuple of distinct positive shifts at most K, and every real cutoff between zero and N, by A N^(1/2+epsilon). For each positive epsilon, one positive A works for all sufficiently large N and every K in the specified length family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("msthird-theorem"),
                DeclarationHandle.Create(Prefix + "MSThirdTheorem"),
                H("Msthird theorem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Montgomery–Soundararajan 2004 Theorem 3 is assumed for k=2 and k=4 under their correlation hypothesis (20), restricted to a specified family of integer lengths. "
                    + "The correlation hypothesis is needed only at each pair (N, K) under consideration, so the same uniform estimate applies on any specified length family. "
                    + "For each positive epsilon, one positive constant bounds the discrete moment minus its logarithmic main term by the explicit error envelope, uniformly for sufficiently large N and log N<=K<=N^(1/k) in that family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("polynomial-length-family"),
                DeclarationHandle.Create(Prefix + "polynomialLengthFamily"),
                H("Polynomial length family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The polynomial length family consists of natural cutoffs N and lengths K satisfying K<=M N^beta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hl4-implies-ms20"),
                DeclarationHandle.Create(Prefix + "hl4_implies_ms20"),
                H("Restricted correlation errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k<=4 and M>=1, the strong Hardy–Littlewood bound with the "
                    + "concrete singular series implies MS20 uniformly for K<=M*N^beta. "
                    + "The real correlation cutoff is restricted to 0<=y<=N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-increment"),
                DeclarationHandle.Create(Prefix + "integer_increment"),
                H("Integer-length increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural n and K, D(K,n) equals the sum of Lambda(n+d)-1 "
                    + "over the integers 1<=d<=K. This identifies the discrete moments "
                    + "with the interval sums used in cumulative sampling."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-length-cell"),
                DeclarationHandle.Create(Prefix + "real_length_cell"),
                H("Flooring the lattice length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For v>=0 and natural n, the interval sum S(v,0,1,n) equals "
                    + "D(floor(v),n). The integer shifts and the centering both use "
                    + "the natural floor of v."))),
                DescribeRole.Theorem))));
}
