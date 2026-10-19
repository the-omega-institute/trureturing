using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class EvenAngleSumObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even number of middle angles cannot sum to two pi.",
        H("Even middle-angle sums cannot close at 2*pi"),
        Blocks(
            Paragraph(Text(
                "Consider a finite family of real angles with even cardinality. If every "
                + "angle lies strictly between pi/3 and pi/2, then the total cannot equal "
                + "2*pi.")),
            Describe.Lean(
                DescribeId.Create("even-middle-angle-sum-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi"),
                H("Even middle angles cannot close"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an empty family the sum is zero. For a nonempty family, write its "
                        + "even cardinality as twice k. If k is at most two, the strict upper "
                        + "bound pi/2 makes the total strictly less than 2*pi. If k is at least "
                        + "three, the strict lower bound pi/3 makes the total strictly greater "
                        + "than 2*pi.")),
                    Paragraph(Text(
                        "This is the numerical angle-budget component of the low-face transport "
                        + "obstruction. It assumes the even-cardinality fact supplied by a "
                        + "separate face-pairing argument and does not itself construct the "
                        + "pairing, classify the six-length shape family, or prove a global "
                        + "geometric realization."))),
                DescribeRole.Theorem))));
}
