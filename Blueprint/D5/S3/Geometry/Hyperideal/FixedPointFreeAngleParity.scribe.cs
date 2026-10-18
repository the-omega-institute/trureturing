using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FixedPointFreeAngleParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-point-free pairing leaves an even middle-angle support.",
        H("Fixed-point-free angle support misses 2*pi"),
        Blocks(
            Paragraph(Text(
                "Let a finite family carry an involution without fixed points. "
                + "Assume the involution preserves each angle and every angle is "
                + "either zero or strictly between pi/3 and pi/2.")),
            Describe.Lean(
                DescribeId.Create("zero-or-middle-angle-sum-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FixedPointFreeAngleParity.zero_or_middle_angle_sum_ne_two_pi"),
                H("Zero-or-middle angle sums miss 2*pi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Restrict the involution to the subtype of nonzero angles. "
                        + "The restriction is still involutive and fixed-point-free, "
                        + "so this subtype has even cardinality. The strict middle-angle "
                        + "budget then places its sum strictly below or above 2*pi; "
                        + "the zero complement contributes nothing."))),
                DescribeRole.Theorem))));
}
