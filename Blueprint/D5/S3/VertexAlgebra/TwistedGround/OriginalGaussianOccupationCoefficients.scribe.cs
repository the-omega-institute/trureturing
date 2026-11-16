using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianOccupationCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianOccupationCoefficients", H("Ordinary energy coefficients of the literal occupation germ"), Blocks(
            Paragraph(Text("At each fixed frequency cutoff, the actual occupation germ converges normally on a positive closed source disk times both external unit polydisks. Exact source scaling turns each summand into a monomial at twice the positive internal energy. Locally uniform derivative convergence at every finite order justifies source extraction. The existing oscillator-energy finiteness theorem makes its energy layer finite. The resulting coefficient is iteratedDeriv at order 2*n divided by (2*n)!, including n=0. No cutoff-independent raw radius is used. The original Wick readout has a common-box energy-layer expression. Its external analytic coefficient identification remains separate.")),

            N("energy_layer_finite", "Finite internal energy layer", "Strictly positive ordinary frequencies make every fixed energy layer finite, including the zero layer and empty internal index types."),
            N("iterated_partial_diff", "Holomorphic finite partial derivatives", "Every finite partial sum of entire source summands has differentiable iterated source derivatives."),
            N("original_finite_mixed_exponent_collect", "Literal finite effective exponent", "The quadratic expression in the two mixed original means collects into the finite effective charge constant, the actual ordered effective covariance and the actual effective mean. Symmetry of the full insertion covariance identifies the two linear cross terms. Products use ordinary transpose, with no conjugation or extra charge half."),
            N("original_finite_sewing_energy_coefficient", "Source coefficient of the literal finite effective generating function", "The same finite energy layer is the 2*n ordinary source coefficient after collecting the actual finite constant, effective covariance and effective mean. The two external variable families remain arbitrary in their unit polydisks. External coefficient extraction and its exchange with source differentiation remain unproved.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-gaussian-occupationcoefficients-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
