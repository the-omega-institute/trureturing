using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class MSConjectureBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjectural prime moments on integer lengths imply uniform second moments and fourth bounds on polynomial bands.",
        H("Conjectural moments on polynomial bands"),
        Blocks(
            Paragraph(Text(
                "Montgomery and Soundararajan, Primes in short intervals, Communications in Mathematical Physics 252 (2004), 589–617, Conjecture 1, is used as a hypothesis for orders two and four. The consequences for floored polynomial bands are derived here. No prime moment conjecture is asserted unconditionally.")),
            Describe.Lean(
                DescribeId.Create("conjecture-two-four"),
                DeclarationHandle.Create(Prefix + "MSConjectureTwoFour"),
                H("The two conjectural moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each k equal to two or four, every fixed positive epsilon and eta admit an integer cutoff beyond which every integer H with (log N)^(1+epsilon)<=H<=N^(1-epsilon) satisfies |M_k(N;H)-mu_k N (H log(N/H))^(k/2)|<=eta N (H log(N/H))^(k/2). Here mu_2=1 and mu_4=3, and M_k sums the kth powers of psi(n+H)-psi(n)-H for 1<=n<=N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conjecture-band-geometry"),
                DeclarationHandle.Create(Prefix + "conjecture_band_geometry"),
                H("The conjectural range after flooring"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1 there is epsilon>0 such that, for all sufficiently large real Y and every Y^alpha<=v<=Y^beta, the natural floors N and H satisfy N>=2, H>=1, (log N)^(1+epsilon)<=H<=N^(1-epsilon), and H<=N. Polynomial growth dominates the logarithmic lower endpoint, while floor_power_upper from the shared single-length band geometry applies the strict upper exponent margin to absorb rounding of Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discrete-second-uniform"),
                DeclarationHandle.Create(Prefix + "conjecture_discrete_second_uniform"),
                H("Uniform discrete variance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the two conjectural moments and fix 0<alpha<beta<1. For every eta>0, eventually uniformly over Y^alpha<=v<=Y^beta, the second discrete moment at the natural floors of Y and v differs from Y v log(Y/v) by at most eta Y v log(Y/v). Rounding the leading term costs at most 4 Y log Y; dividing by the band normalizer makes this error vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discrete-fourth-upper"),
                DeclarationHandle.Create(Prefix + "conjecture_discrete_fourth_upper"),
                H("Uniform discrete fourth bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same conjecture and exponent conditions, there exists A>=1 such that eventually M_4(floor Y;floor v)<=A Y v^2 (log Y)^2 uniformly over the band. The proof takes A=4: relative conjectural error one adds to the Gaussian coefficient three, and flooring only decreases each factor in this upper bound."))),
                DescribeRole.Theorem))));
}
