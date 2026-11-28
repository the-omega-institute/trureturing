using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalQuaternionReadingRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Which signed probe differences can an entire group realize?",
        H("Rational quaternion realization of three readings"),
        Blocks(Describe.Lean(DescribeId.Create("whole-group-reading-realization"),
            DeclarationHandle.Create("D5/S3/Quantum/AURICOmega/RationalQuaternionReadingRealization.exists_rational_group_kernel_with_readings"),
            H("Prescribed rational overlap and signed probe difference"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let t and d be rational, with t nonnegative and d squared at most "
                    + "one minus t. There is a nonabelian group G, a rational kernel K on G, and "
                    + "two points y and z such that K(1, y) equals t and K(1, z) minus K(y, z) "
                    + "equals d. The same symmetric kernel takes values in [0, 1], takes the "
                    + "value one precisely on the diagonal, and attains zero. Both left and "
                    + "right translation preserve all readings. Every finite Gram form is "
                    + "nonnegative for weights in any linearly ordered field.")),
                Paragraph(Text("Choose positive rational parameters A and B in a quaternion algebra. "
                    + "The group consists of the rational elements of weighted square norm one. "
                    + "The kernel is half of one plus their weighted inner product. Multiplicativity "
                    + "of the norm gives both translation laws, and the finite Gram form is a sum "
                    + "of five weighted squares. The negative identity has zero reading against "
                    + "the identity. Explicit elements in the i and j directions do not commute.")),
                Paragraph(Text("Choose y with real component 2t − 1. For t below one, take the "
                    + "component of z along 1 − y to be d times (1 − y) divided by 2(1 − t). "
                    + "A perpendicular coordinate fills the remaining square norm "
                    + "1 − d²/(1 − t). At t equal to one, d is zero and y and z may both be the "
                    + "identity. The group and the kernel may depend on the pair (t, d). "
                    + "The construction prescribes the mutual reading and the signed difference, "
                    + "leaving the individual probe readings free."))),
            DescribeRole.Theorem)),
        []));
}
