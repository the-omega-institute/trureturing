using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class SeparatingPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separating Points", H("Separating Points"),
        Blocks(
            Paragraph(Text("Very general point of a holomorphic family by Baire; countable residue fields. Schematically dense complex points determine functions, morphisms and maps to projective space.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/SeparatingPoints.exists_map_of_coords"),
                H("exists_map_of_coords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let e_z, p_z be complex points of S-schemes X, G over the same η_z, with X reduced and the e_z dense. If a linear system W on X and a projective embedding M of G give e_z, p_z the same homogeneous coordinates, then some S-morphism d : X → G has d∘e_z = p_z and d^*M = W.")))))));
}
