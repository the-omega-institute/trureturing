using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMEnergyCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFourMEnergyCoefficient", H("Original fourM total-energy coefficient"), Blocks(
            Paragraph(Text("At total energy E, the source mode is H+K-E-1. Each integral charge q in the specified mod-two coset contributes at charge energy m = (q,q)/2 and oscillator energy E-m. Its charge factor is 16 raised to the power -m. The formal shift by m multiplies the even ordinary sewn coefficients by the m-th power of the square coordinate. The coefficient of index 2(E-m) already contains its ordinary Taylor normalization.")),
            Paragraph(Text("The finite two-index left lowering retains both lowering factorials. Expanding the four external polynomials gives four independent occupation factorials and the two original Laurent selectors. The left sign is the product of the lowering sign with the degree sign from substituting the negative square coordinate.")),
            N("oscillatorKernel_reflected", "Reflection at the original left Laurent mode",
                "The reflected charge and oscillator polynomial give the same exact left kernel because its Laurent exponent is even. The ground action agrees after reducing the charge modulo two."),
            N("cosetKernel_unreflected", "Evaluation of the reflected half-average",
                "The average of the original and reflected kernels is evaluated inside the finite energy fiber, with the right leg and the two charge scalars retained."),
            N("fourM_energy_coefficient", "Actual total-energy diagonal",
                "The original scalar on rank-24 homogeneous tensor inputs equals the degree-E coefficient of the negative-coordinate coset series, multiplied in each coset by the two original ground-form coefficients in their original order."),
            N("fourM_negative_energy", "Negative intermediate energy",
                "Nonnegative charge and oscillator energies make the original intermediate fiber empty and the scalar zero."),
            N("lowered_left_selector", "Left lowering weights and exponent",
                "Each nonzero occupation of a lowered homogeneous tensor factor has doubled weight twice the original weight minus three and minus twice the lowering index. The resulting left exponent satisfies the original Laurent selector throughout the charge sublevel."),
            N("right_selector", "Right Laurent mode and parity",
                "For an even right weight difference, the selector is one exactly at t = E-1 plus half that difference. For an odd difference it is zero.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-fourm-energy-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
