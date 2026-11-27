using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class ConjugateJetDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate Jet Defs", H("Conjugate Jet Defs"),
        Blocks(
            Paragraph(Text("Definition of tight frames in the unimodular lattice, with multiplicities. Definition: orthogonality relation between translates of the vacuum and of a finite vector. Relation: jets of one vector are Galois conjugates of those of another.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/ConjugateJetDefs.IsJetConjugate"),
                H("IsJetConjugate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The series T_t f with σ applied to its coefficients equals T_{t'} f' with the places of its variables renamed by π⁻¹.")))))));
}
