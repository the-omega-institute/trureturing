using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class JointDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible joint depth binds logarithmic scale and W-indexed phase resolution to the same point.",
        H("Admissible Joint Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-joint-scale-digit-phase-depth"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/JointDepth.joint_depth_spec"),
                H("Admissible joint scale, digit, phase, and depth"),
                StatementSource.FromAuthor(
                    FormulaDsl.Disp(FormulaDsl.Id("jointDepthSpec"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero golden integer supplies both the logarithmic scale and the admissible W-resolution index. Canonical digits and circle phase come from the natural coordinate, and the dependent finite bucket records the resulting depth without truncating a negative index."))),
                DescribeRole.Definition
            ))));
}
