using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class CommonEigenvectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common Eigenvectors", H("Common Eigenvectors"),
        Blocks(
            Paragraph(Text("Auerbach's lemma: basis dual to chosen forms with all forms bounded by one. Steinitz: embeddings of a countable ring extend to field isomorphism with C. Embeddings of countable rings into C extend to fields of continuum size. Semisimplicity by trace form, free integers, minors criterion for linear dependence. Common eigenvectors and eigencharacters of commuting operators; sorting by adjacent swaps.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/CommonEigenvectors.exists_eigencharacter"),
                H("exists_eigencharacter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A representation of a commutative monoid on a non-zero finite-dimensional space over an algebraically closed field has a common eigenvector, and its eigenvalues form a character.")))))));
}
