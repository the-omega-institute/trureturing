using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMChargeNormalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.";

    private static DocumentBlock Result(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal convergence of the original fixed four-point occupation over charges.",
        H("Normal Convergence of the Original Four-Point Charge Sum"),
        Blocks(
            Result("compact-charge-normal", "compact_charge_normal", "Summable compact majorant",
                "Fix the compact external labels and occupation of the four-point energy coefficient. "
                + "On a compact chart, the scalar and covariance are bounded. The signed mean grows "
                + "linearly in the charge size. The finite native affine coefficient has charge growth "
                + "bounded by an occupation-dependent power. The original nome to the exact charge "
                + "energy makes that bound summable, and the charge sum is holomorphic in the interior."),
            Result("sewn-charge-normal-at-zero", "sewn_charge_normal_at_zero", "Original sewn terms near zero",
                "In the sewing coordinate z, the source scalar, energy shift, and two charge factors "
                + "give Q₀(z²) to the charge energy. The affine coefficient retains the literal signed "
                + "mean and sewn covariance. A closed disk about zero admits a summable bound for "
                + "every charge and the resulting sum is holomorphic on its interior."),
            Result("sewn-charge-coefficient", "sewn_charge_coefficient", "Charge-class Taylor coefficient",
                "At order 2E in the sewing coordinate, local uniform convergence permits the "
                + "Taylor coefficient to pass through the charge sum. Only charges of energy at "
                + "most E contribute. Each surviving coefficient is the degree-E coefficient of "
                + "the original square-coordinate charge series in that charge class."))));
}
