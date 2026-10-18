using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class RegularDegreeAngleStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree-normalized angles give exact global edge sums and a strict local vertex bound.",
        H("Degree-normalized strict angle structure"),
        Blocks(
            Paragraph(Text(
                "For a finite paired tetrahedral family, degree(q,e) is the number of actual "
                + "edge occurrences in the global edge class e, and regularAngle(q,o) is "
                + "2*pi divided by the degree of the global edge containing occurrence o.")),
            Describe.Lean(
                DescribeId.Create("regular-degree-angle-structure"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/RegularDegreeAngleStructure.regular_degree_angle_structure"),
                H("Minimum degree eight gives a strict angle structure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume every actual global edge has degree at least eight. Then every "
                        + "regularAngle is positive, the M sum over every global edge is exactly "
                        + "2*pi, and every local Q sum is at most 3*pi/4 and therefore strictly "
                        + "less than pi.")),
                    Paragraph(Text(
                        "The local estimate uses the six tetrahedral edge slots and the fact that "
                        + "at most three slots meet a local vertex; each nonzero contribution is "
                        + "at most pi/4. The theorem concerns the angle structure supplied by the "
                        + "actual pairing. It does not construct common edge lengths, prove a "
                        + "global gluing, establish a general geometric realization, or settle "
                        + "later degeneracy and volume questions."))),
                DescribeRole.Theorem))));
}
