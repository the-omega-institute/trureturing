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
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("rotation-orbit-gaps-partition"),
                    H("Rotation orbit gaps partition the circle"),
                    LeanTheorem(
                        "D5/S1/Recurrence/RotationOrbitGapsPartition."
                        + "rotation_orbit_gaps_partition"),
                    LatexStatement.Create(
                        @"$$\forall \alpha\in\mathbb{R},\ n\in\mathbb{N},\ "
                        + @"O_{\alpha,n}:=\operatorname{rotationOrbit}(\alpha,n)="
                        + @"\{\operatorname{fract}(k\alpha)\mid k\in\mathbb{N},\ k<n\}:\ "
                        + @"O_{\alpha,n}\subseteq[0,1)\ \land\ "
                        + @"(0<n\Rightarrow O_{\alpha,n}\neq\emptyset)\ \land\ "
                        + @"\forall h_n:0<n,\ "
                        + @"((\forall x\in O_{\alpha,n},\ "
                        + @"g_{O_{\alpha,n},h_n}(x)>0)\ \land\ "
                        + @"\sum_{x\in O_{\alpha,n}}g_{O_{\alpha,n},h_n}(x)=1).$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The fractional parts of the first n multiples of a real rotation "
                        + "parameter lie in the half-open unit interval. For positive n, "
                        + "the orbit contains its zeroth point, so the cyclic gap partition "
                        + "applies: every clockwise gap is positive and their sum is one. "
                        + "At parameter one half and length two, the orbit is exactly zero "
                        + "and one half; zero uses the ordinary successor while one half "
                        + "uses the wrap branch.")))))));
}
