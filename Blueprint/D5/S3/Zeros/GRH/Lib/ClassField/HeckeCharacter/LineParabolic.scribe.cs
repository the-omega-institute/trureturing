using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class LineParabolicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Parabolic", H("Line Parabolic"),
        Blocks(
            Paragraph(Text("Tamely ramified characters, local components and residues; data and theta integrals named. Equivariant maps from local data to automorphic functions; real sign classes. Coordinates on radical and Levi factor of an isotropic line stabiliser.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LineParabolic.lineLevi"),
                H("lineLevi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The homomorphism from ideles × U(V)(𝔸) to the Levi subgroup sending (a,g) to the element acting by a⁻¹ on the line k and by g on V.")))))));
}
