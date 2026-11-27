using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class IntegralLinkRestrictionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/IntegralLinkRestriction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact integral image of signed restriction to an independent matroid link.",
        H("Integral lifting through matroid links"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-link-lift"),
                DeclarationHandle.Create(Module + ".exists_topCycle_linkRestrict_singleton"),
                H("Lifting through a singleton link"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite totally ordered carrier and a matroid on it. At a face "
                        + "avoiding the contracted vertex, signed link restriction reads the coefficient "
                        + "with that vertex inserted and multiplies it by its insertion sign. The map "
                        + "is zero at faces containing the vertex. If the vertex is a nonloop and a "
                        + "noncoloop, every integral augmented top cycle of its contraction lifts.")),
                    Paragraph(Text(
                        "Place the vertex last, preserving the order on the other vertices. "
                        + "An internally passive basis of the contraction extends to an internally "
                        + "passive basis of the original matroid. Exchanges in the contraction lift, "
                        + "and the noncoloop hypothesis supplies an exchange at the last vertex. "
                        + "The normalized integral cycles on the extended bases give the lift by a "
                        + "finite integer sum.")),
                    Paragraph(Text(
                        "A face containing the moved vertex changes orientation once for each "
                        + "vertex it crosses. The resulting signs intertwine the boundary operators "
                        + "in the two orders. The lifted chain therefore has vanishing boundary in "
                        + "the original order, including its augmented coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-face-link-image"),
                DeclarationHandle.Create(Module + ".exists_topCycle_linkRestrict_iff_coloop"),
                H("The image of an independent-face link restriction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an independent face, read the coefficient at its union with a disjoint "
                        + "face and multiply by the shuffle sign of the two faces. Set other "
                        + "coordinates to zero. The image consists of the integral augmented top "
                        + "cycles of the contraction, with the additional condition that the "
                        + "image cycle is zero whenever the contracted face contains a coloop.")),
                    Paragraph(Text(
                        "Compose singleton restrictions with the restriction to the remaining "
                        + "face. The shuffle signs differ from the single restriction by the "
                        + "insertion sign of the singleton in that face. This sign squares to one "
                        + "and can be absorbed into the lifted cycle. Contraction preserves the "
                        + "absence of coloops among the surviving vertices."))),
                DescribeRole.Theorem))));
}
