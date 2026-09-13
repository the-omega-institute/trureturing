using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class JointRotationFactorComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint Rotation Factor Complexity.",
        H("Joint Rotation Factor Complexity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jointrotationfactorcomplexity-joint-bound"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/JointRotationFactorComplexity.joint_rotation_factor_complexity"),
                H("A linear bound for simultaneous rotation words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be a finite nonempty set of positive integer scales, let alpha be irrational, "
                    + "and choose an integer offset b(a) at each scale. At phase x and time j, the "
                    + "coordinate at scale a is b(a) minus the indicator that the fractional part "
                    + "of a(x + j alpha) + alpha is at least one minus the fractional part of a alpha. "
                    + "For positive h, the set of length h vector words realized by x in [0,1) is finite and has "
                    + "cardinality at most (h + 1) times the sum of the scales in A. "
                    + "All coordinates use the same circle phase. Cutting the circle at one of "
                    + "the floor discontinuities allows the h + 1 floor samples at every scale "
                    + "to be counted together; equal cumulative counts determine equal vector words. "
                    + "The bound includes boundary phases."))),
                DescribeRole.Theorem))));
}
