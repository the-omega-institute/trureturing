using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class RotationOrbitGapsPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/RotationOrbitGapsPartition",
                "Finite rotation orbit gaps partition the unit circle."),
            H("Rotation Orbit Gap Partition"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("rotation-orbit-gaps-partition"),
                    DescribeKind.Theorem,
                    H("Rotation orbit gaps partition the circle"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Recurrence/RotationOrbitGapsPartition."
                        + "rotation_orbit_gaps_partition")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The fractional parts of the first n multiples of a real rotation "
                        + "parameter lie in the half-open unit interval. For positive n, "
                        + "the orbit contains its zeroth point, so the cyclic gap partition "
                        + "applies: every clockwise gap is positive and their sum is one. "
                        + "At parameter one half and length two, the orbit is exactly zero "
                        + "and one half; zero uses the ordinary successor while one half "
                        + "uses the wrap branch."))),
                    LatexStatement.Create(
                        @"$$0<n\Rightarrow g_{O_{\alpha,n}}(x)>0\ (x\in O_{\alpha,n}),"
                        + @"\qquad \sum_{x\in O_{\alpha,n}}g_{O_{\alpha,n}}(x)=1.$$")))));
}
