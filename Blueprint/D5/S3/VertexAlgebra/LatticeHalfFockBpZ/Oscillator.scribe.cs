using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class OscillatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex-bilinear form on the actual half-integer polynomial Fock space has the BPZ current sign.",
        H("Half-Integer Oscillator BPZ Pairing"),
        Blocks(Describe.Lean(
            DescribeId.Create("oscillatorcurrentadjoint"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Oscillator.oscillator_current_adjoint"),
            H("Reflected Native Current Adjoint"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The existing gramBilinear is complex-linear in each argument. For mode n choose a nonzero complex scalar whose square is -(n+1/2)/(n+1), and apply the resulting invertible polynomial substitution to both arguments. This defines oscillatorPairing as a BilinForm, not a sesquilinear form. The substitution intertwines the original integer annihilator with its scalar multiple; the square of the scalar converts the original contraction to the actual negative half-integer contraction.")),
                Paragraph(Text("The underlying integer form and its radical theorem are reused from LatticeOscillatorFockForm and LatticeOscillatorFockMetric. The coefficient conjugation involution gives an explicit bridge to the existing radical theorem; no positivity assertion defines the new form. Symmetry and both zero radicals follow along the proved invertible substitution, with both inverse-Gram equations retained.")),
                Paragraph(Text("For the actual current at index j the adjoint is minus the current at index -j-1. Creation is multiplication by the original variable; annihilation is the original Gram-weighted derivative multiplied by j+1/2. The identity is uniform over all integer modes and all finite-support polynomials."))),
            DescribeRole.Theorem))));
}
