using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PhysicalCosineTailProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete complex Lebesgue L2 cosine-tail projections and two-cutoff bounds for physical shifts and the finite prime action.",
        H("Physical cosine tail projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-l2"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.WindowL2"),
                H("The original complex Lebesgue L2 carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("windowMeasure(a) is Lebesgue measure restricted to the physical window Ioc(-a,a], and WindowL2(a) is Lp of complex functions with exponent two for that measure. These are AE classes. The carrier definitions allow arbitrary real a, while normalized orthonormality and the concluding estimates require a>0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mode-l2"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.modeL2"),
                H("The original normalized cosine as an L2 class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("modeL2(a,n) is the MemLp class of the real mode cast into complex values. The frequency is 2*pi*n/(2*a); amplitude is 1/sqrt(2*a) at n=0 and sqrt(2/(2*a)) otherwise. Boundedness and continuity on the finite window provide MemLp without imposing positivity on a in this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modes-orthonormal"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.modes_orthonormal"),
                H("Physical cosine orthonormality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, the existing physical matrixEntry at zero shift gives the complex L2 Gram matrix: one on the diagonal and zero off it, including the constant mode. This proves orthonormality of all natural modes on physical dx, rather than assuming it or changing to normalized Haar measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("head-l2"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.headL2"),
                H("Finite complex cosine head"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural N and arbitrary complex v, the head sums v(n) times modeL2(a,n) for n in range(N+1), including zero and N. Under a>0 its squared norm is headMass(N,v), the sum of squared complex coefficient norms. This normalization is used to turn coefficient estimates into the concluding L2 estimates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shift-head-l2"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.shiftHeadL2"),
                H("The actual compressed shift as an L2 class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("shiftHeadL2 is the L2 class of compression(a,s,profile(a,range(N+1),v)). The profile is zero-extended before translation by the arbitrary real s and then compressed again to Ioc(-a,a]. Indicator measurability and the finite profile bound establish MemLp. Its inner product with modeL2(a,m) is the original integral shiftCoefficient, preserving the complex linear sum and every mixed coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-head-l2"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.primeHeadL2"),
                H("The original finite symmetric prime image in L2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum runs over r in Icc(1,primeCutoff(a)), with primeCutoff(a)=floor(exp(2*a)) and weight vonMangoldt(r)/sqrt(r). It retains the L2 compressed shifts at log(r) and -log(r) separately. The arithmetic cutoff is distinct from the natural head cutoff N and the later natural exterior cutoff M; no primality-only filter is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-image-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.primeHeadL2_ae_action"),
                H("The L2 representative is the exact original prime action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real a, natural N and complex v, the representative agrees almost everywhere for windowMeasure(a) with primeAction(a,primeCutoff(a),profile(a,range(N+1),v)). This identifies the finite L2 construction with the existing pointwise action. Its mode inner products are consequently the actual primeCoefficient integrals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-cosine-tail"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.exteriorSpace"),
                H("Closed span of all modes above M"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural M, the tail is the topological closure of the complex span of modeL2(a,M+j+1), with j ranging over all natural numbers. The closed subtype is complete. For a>0 the restricted modes form a Hilbert basis of this closed span by construction. This module does not define the original AE-even sector as a cosine span or identify the tail with its head complement; those identifications are established separately by OriginalEvenCosineComplete and OriginalEvenExterior."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exterior-projection"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.exteriorProjection"),
                H("Orthogonal projection onto the concrete closed tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuous complex linear map has domain WindowL2(a) and codomain exteriorSpace(a,M). There is no upper tail truncation. Under a>0, Parseval for the constructed tail Hilbert basis identifies its squared norm with the infinite sum of squared inner products against all original modes M+j+1. Only completeness inside this closed span is used here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shift-projection-bound"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.shift_projection_bound"),
                H("L2 tail bound for an actual compressed shift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume a>0, natural N and M with N<M, arbitrary complex v and arbitrary real s. The squared exterior projection norm is at most (N+1)/(pi^2*(M-N)) times the squared headL2 norm, with natural numbers cast to reals in the denominator. Tail Parseval, the exact shift coefficient identity and shift_complete_tail give this bound. No shift-size restriction is needed, since the actual compressed pairing vanishes outside support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-projection-bound"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection.prime_projection_bound"),
                H("L2 two-cutoff bound for the actual symmetric prime image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume a>0 and natural N<M, with arbitrary complex v. The squared projection norm is at most 4*primeMass(a)^2*(N+1)/(pi^2*(M-N)) times the squared original head norm. primeMass is the exact finite sum of von Mangoldt weights up to primeCutoff(a). The factor four retains the triangle bound for both signed shifts after squaring; no phase averaging or cancellation premise is used. The proof transports prime_complete_tail through the concrete tail Parseval identity.")),
                    Paragraph(Text("These are applications of standard Lebesgue L2, cosine orthonormality, Hilbert bases and orthogonal projection. They are analytic support estimates, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed."))),
                DescribeRole.Theorem))));
}
