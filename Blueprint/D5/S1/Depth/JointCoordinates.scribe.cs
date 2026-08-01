using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class JointCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Depth/JointCoordinates",
            "Joint golden coordinates combine logarithmic scale, canonical W digits, circle phase, and finite depth."),
        H("Joint Golden Coordinates"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("joint-scale-digit-phase-and-finite-depth"),
                H("Joint scale, digit, phase, and finite-depth coordinates"),
                LeanTheorem(
                    "D5/S1/Depth/JointCoordinates.joint_coordinates_spec"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A nonzero golden integer receives an option-valued logarithmic scale, while a positive natural point supplies its canonical W row and circle phase. The same statement records the W-indexed resolution and its dependent finite phase bucket.")))
            ))));
}
