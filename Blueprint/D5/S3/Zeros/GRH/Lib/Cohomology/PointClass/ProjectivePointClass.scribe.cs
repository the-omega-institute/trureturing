using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class ProjectivePointClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective Point Class", H("Projective Point Class"),
        Blocks(
            Paragraph(Text("Hodge–Tate map does not kill the class of a point of projective space.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/ProjectivePointClass.hodgeTateMap_pointClass_ne_zero"),
                H("hodgeTateMap_pointClass_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a field k with an embedding in Q̄_p and any k-point z of projective d-space projSpace, the Hodge–Tate map of weight d does not kill the class cl(z) ∈ Hdg^d.")))))));
}
