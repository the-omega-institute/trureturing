using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMCurrentRegressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two same-puncture currents in modes one and zero",
        H("The fixed-charge chart A coefficient and inverse lowering"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-two-mark-fixed-charge"),
                DeclarationHandle.Create(Prefix + "chartA_same_puncture_modes_one_zero_fixed_charge"),
                H("The physical coefficient at fixed charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a lattice colour and a charge of nonnegative energy. For either "
                    + "lip and real 1/2 < x < 1, take degree one in each independent mark at the first "
                    + "A-chart puncture and displacement degrees one and zero. Normalize by the inverse "
                    + "twelfth power of the A period. The result is (1−t)³ divided by the square of the "
                    + "first puncture's scale, times the sum of three native slit charge terms. Their "
                    + "occupations and multipliers are one mode-one and one mode-zero current with "
                    + "multiplier one, two mode-zero currents with multiplier −3, and the vacuum "
                    + "with multiplier 3/16 of the diagonal Gram entry. The other punctures are in vacuum "
                    + "and the slit parameter is t = 1−1/x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-two-mode-oscillator-lowering"),
                DeclarationHandle.Create(Prefix + "lowering_modes_one_zero"),
                H("Powers of oscillator lowering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the Gram determinant is a unit. Apply the nth power of "
                    + "oscillator lowering to the product of mode-one and mode-zero creation variables "
                    + "of the same colour, and divide by n factorial. The outputs for n = 0, 1 and 2 "
                    + "are the input, 3/2 times the square of the mode-zero variable, and the vacuum "
                    + "scaled by 3/16 times the diagonal Gram entry. All higher powers vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-two-mark-factorial-lowering"),
                DeclarationHandle.Create(Prefix + "chartA_same_puncture_modes_one_zero_lowering"),
                H("The finite factorial-weighted readout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With unit Gram determinant and the same physical hypotheses, "
                    + "form the inverse lowering sum over k = 0, 1, 2, 3 with coefficient (−1)ᵏ/k! "
                    + "on the kth power. The normalized physical coefficient equals the sum over the "
                    + "resulting polynomial's support, weighting each coefficient by the occupation "
                    + "factorial and the fixed-charge slit term at that occupation, with the common "
                    + "factor (1−t)³ divided by the square of the scale. The repeated mode-zero "
                    + "occupation has factorial two, giving the multiplier −3."))),
                DescribeRole.Theorem))));
}
