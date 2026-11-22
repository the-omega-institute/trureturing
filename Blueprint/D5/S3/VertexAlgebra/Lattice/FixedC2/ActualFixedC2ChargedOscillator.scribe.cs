using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2ChargedOscillatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quadratic modes reduce every single oscillator on a charged orbit.",
        H("Single Oscillators on Fixed Charge Orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-quadratic-product"),
                DeclarationHandle.Create(Prefix + "fixed_charged_quadratic_product"),
                H("The quadratic minus-one mode on a charged ground"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual mode with neutral factors X(i,k) and X(j,0) on a "
                    + "fixed charged ground has the paired two-oscillator polynomial as its creation "
                    + "term. The two contractions produce single oscillators at index k+1, weighted "
                    + "by the corresponding Gram pairings with factors k+1 and (-1)^k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-higher-oscillator-isolation"),
                DeclarationHandle.Create(Prefix + "fixed_higher_oscillator_mem"),
                H("Weighted quadratic modes isolate higher oscillators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weight the quadratic products by the coordinates of the "
                    + "charge and subtract the translation of the single oscillator at index k. "
                    + "Translation lies in C2 and cancels the two-oscillator term. For squared norm "
                    + "B, the coefficient of the oscillator at index k+1 is A = (k+1)(B-1), along "
                    + "with a term in the charge direction. Summing again against the charge "
                    + "coordinates isolates that direction with coefficient A + (-1)^k B. For "
                    + "B ≥ 4 both coefficients are nonzero. One can recover each single oscillator "
                    + "in any subspace containing C2 and the weighted quadratic products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-charge-orbit"),
                DeclarationHandle.Create(Prefix + "fixedChargeOrbit"),
                H("Fixed states supported on a charge and its negative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed charge orbit space consists of fixed states "
                    + "supported on the pair of charges c and -c. Neutral quadratic modes preserve "
                    + "this support because each constituent neutral current acts within one "
                    + "charge fiber."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-single-orbit-reduction"),
                DeclarationHandle.Create(Prefix + "fixed_charged_oscillator_mem_sup_orbit"),
                H("Ground charge reduction extends to all single oscillators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the fixed ground of squared norm at least four lies "
                    + "in the sum of intrinsic C2 and a target orbit space. Neutral quadratic zero "
                    + "modes and minus-one modes preserve that sum. The zero-mode calculation gives "
                    + "the first oscillator there, and the weighted minus-one calculation gives "
                    + "every higher single oscillator in the same sum."))),
                DescribeRole.Theorem))));
}
