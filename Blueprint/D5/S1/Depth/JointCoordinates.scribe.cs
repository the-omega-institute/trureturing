using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class JointCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint golden coordinates combine logarithmic scale, canonical W digits, circle phase, and finite depth.",
        H("Joint Golden Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-scale-digit-phase-and-finite-depth"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/JointCoordinates.joint_coordinates_spec"),
                H("Joint scale, digit, phase, and finite-depth coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero golden integer receives an option-valued logarithmic scale, while a positive natural point supplies its canonical W row and circle phase. The same statement records the W-indexed resolution and its dependent finite phase bucket."))),
                DescribeRole.Definition
            ))));
}
