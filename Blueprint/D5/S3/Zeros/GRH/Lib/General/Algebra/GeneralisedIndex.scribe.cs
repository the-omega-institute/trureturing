using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class GeneralisedIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generalised Index", H("Generalised Index"),
        Blocks(
            Paragraph(Text("Generalised index is invariant under the involution; lattice index is index of the determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/GeneralisedIndex.submoduleIndex_colLattice_div"),
                H("submoduleIndex_colLattice_div"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For M in GL_n(A) and L = MRⁿ the lattice spanned by its columns, [Rⁿ : Rⁿ ∩ L]/[L : Rⁿ ∩ L] equals the generalised index [R : (det M)R], when R ⊂ A satisfies IsAdelic.")))))));
}
