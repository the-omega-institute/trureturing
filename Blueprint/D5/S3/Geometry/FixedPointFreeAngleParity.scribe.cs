using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FixedPointFreeAngleParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FixedPointFreeAngleParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-point-free involution forces an interval-bounded angle sum away from two pi.",
        H("Fixed-point-free angle parity obstruction"),
        Blocks(
            Paragraph(Text(
                "Let a finite family carry a fixed-point-free involution. Its cardinality is "
                    + "even. If every angle lies strictly between pi/3 and pi/2, the sum "
                    + "cannot equal 2 pi: the cases of zero, two, or four angles are "
                    + "strictly below 2 pi, while six or more angles are strictly above it.")),
            Paragraph(Text(
                "The statement is an abstract parity and interval obstruction. It supplies "
                    + "the numerical counting step used when a geometric pairing transports "
                    + "a fixed-point-free involution across the finite set of relevant edge "
                    + "occurrences. It does not assert the geometric hypotheses that produce "
                    + "that involution.")),
            Describe.Lean(
                DescribeId.Create("fixed-point-free-angle-parity-obstruction"),
                DeclarationHandle.Create(Prefix + "fixed_point_free_involution_interval_sum_ne_two_pi"),
                H("Fixed-point-free angle sum obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite type with an involutive fixed-point-free self-map, any "
                        + "real-valued angle function whose values all lie in the open "
                        + "interval (pi/3, pi/2) has total sum different from 2 pi."))),
                DescribeRole.Theorem)),
        []));
}
