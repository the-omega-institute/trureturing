using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme;

internal sealed class ThetaFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Family", H("Theta Family"),
        Blocks(
            Paragraph(Text("Isogenies are finite flat; homomorphisms killing the kernel factor through them. Uniqueness of linear lifts, lattice index as determinant norm, number of torsion points. Theta-embedded PEL families, their objects, pull-backs, full level structures, logarithm along a line.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/ThetaFamily.exists_pullback"),
                H("exists_pullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let R be a local ring, φ : R → ℂ a local homomorphism and y' the pull-back of the object y along φ. For every full structure on y, pulling back its sections gives a full structure on y'.")))))));
}
