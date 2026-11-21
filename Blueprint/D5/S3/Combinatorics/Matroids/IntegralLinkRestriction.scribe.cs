using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class IntegralLinkRestrictionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/IntegralLinkRestriction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral top cycles lift through signed restriction to an independent matroid link.",
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
                DescribeRole.Theorem))));
}
