using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class JointDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Depth/JointDepth",
            "Admissible joint depth binds logarithmic scale and W-indexed phase resolution to the same point."),
        H("Admissible Joint Depth"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("admissible-joint-scale-digit-phase-depth"),
                H("Admissible joint scale, digit, phase, and depth"),
                LeanTheorem(
                    "D5/S1/Depth/JointDepth.joint_depth_spec"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A nonzero golden integer supplies both the logarithmic scale and the admissible W-resolution index. Canonical digits and circle phase come from the natural coordinate, and the dependent finite bucket records the resulting depth without truncating a negative index.")))
            ))));
}
