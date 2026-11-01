using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite original-source inverse evaluated in the actual four-M scalar channel.",
        H("Original Four-M Contraction"),
        Blocks(
            Paragraph(Text("The lattice datum, original charge/occupation carrier, theta involution, selected actual tensor pairing and correctedField are unchanged. Assume determinant-unit D, positive definite real Gram matrix and rank 24. Let u and v be the original negative-parity twisted tensors with actualTensorL0 eigenvalues H and K, where H,K are natural numbers. The remaining actual tensors w,d are arbitrary, hence include every homogeneous choice. Both standard modes k,t are signed integers. No source operator is identified with tensor lowering.")),
            Describe.Lean(DescribeId.Create("original-four-m-contraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction.fourM_contraction"),
                H("The actual finite scalar coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Set h=H+K-k-1 and f=normalizedCoefficient D hu k u v h. E is the existing FixedGradedDuality.fixedGradeDualEquiv for sourcePairing, transported only between the two orders of the grade/fixed subtypes, and x=E.symm f. Its original source-pairing evaluation law is used, rather than assuming the explicit inverse to be computed. The actual scalar test is g(a)=actualForm D hu d ((correctedField D hu a).coeff (-2*t-2) w).")),
                    Paragraph(Text("F is the actual homogeneous mixed kernel: sum over p<K-1 and q<H-1, with s=k+1-p-2H+q, of (-1)^(H+s)/(p!q!) times actualForm(C^p v, correctedField(a).coeff(2s)(C^q u)), where C is the existing actual tensor L1. native_kernel_restriction proves that F restricted to the original fixed grade h is precisely f, using MixedIntertwiner.homogeneous_coefficient. Thus no full-carrier dual is confused with a fixed-grade dual.")),
                    Paragraph(Text("The theorem proves g(x)=one half times the sum over the entire EnergyFiber D h of [F(b_a)+F(theta b_a)]g(d_a). Here b_a is the original carrierBasis and d_a=dualCarrierBasis D a reverses charge, substitutes X(i,r) by the sum_j (-(r+1)) inverse times Gcomplex inverse[j,i] times X(j,r), and divides by every occupation factorial. inverse_contraction_half_average is applied to the genuine ambient F and g with the proved restriction law, retaining exactly one original source half-average.")),
                    Paragraph(Text("A second equality proves the signed branches: zero when h<0; f(gradeVacuum) times g(vacuum) when h=0, with the exact equality transport; and the projected finite sum f(fixedFrame a)g(fixedDualFrame a) otherwise. This actively consumes inverse_contraction_signed, including its negative-energy, genuine vacuum and finite-frame dependencies. Positive definiteness is used for the existing finite-grade duality and finite energy fibers; no toNat truncation replaces signed grades."))
                ), DescribeRole.Theorem),
            Paragraph(Text("This is the algebraic contraction of the literal native scalar channel, using the explicit inverse computed in OriginalSourceCoevaluation. It does not supply a common rational or analytic four-point function, Gaussian attribution, crossing, three-M cancellation, fusion, anomaly classification, complete string theory or AdS/CFT. Original ground dimension 4096, all 2^24 cosets, determinant-12 and charge16 normalizations, and nome exp(pi*i*tau) are untouched. This is an application and explicit coefficient computation, with no literature novelty claim."))
        ), []));
}
