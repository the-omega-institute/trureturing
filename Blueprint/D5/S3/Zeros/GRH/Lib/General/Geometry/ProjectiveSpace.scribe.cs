using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ProjectiveSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective Space", H("Projective Space"),
        Blocks(
            Paragraph(Text("Picard group of a scheme, pull-back, fpqc descent of sections and frames. Projective space over Z, O(1), linear systems, maps to projective space, projective embeddings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ProjectiveSpace.exists_hom_projSpace"),
                H("exists_hom_projSpace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A linear system N indexed by κ on X, with any s: X → S, is the pull-back of O(1), cover and transition functions included, along some morphism X → ℙ^κ × S over S.")))))));
}
