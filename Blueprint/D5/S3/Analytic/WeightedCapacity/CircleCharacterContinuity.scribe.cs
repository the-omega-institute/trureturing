using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class CircleCharacterContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle Characters on Capacity States.",
        H("Circle Characters on Capacity States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("circlecharactercontinuity-mass-finite-of-continuousat"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/CircleCharacterContinuity.mass_finite_of_continuousAt"),
                H("Continuity forces finite weighted absolute mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any sequence of natural capacities and any total row of circle points, "
                    + "continuity of the associated character at one finite capacity state implies "
                    + "that the sum of each capacity times the absolute centered representative is finite. "
                    + "A finite coordinate neighborhood controls all admissible tail states. "
                    + "Single-coordinate multiples and separate positive and negative sums then bound "
                    + "the tail mass without assigning a group structure to the capacity states."))),
                DescribeRole.Theorem))));
}
