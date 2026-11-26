using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class FrobeniusOnRootsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius On Roots", H("Frobenius On Roots"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/FrobeniusOnRoots.exists_apply_eq_pow"),
                H("exists_apply_eq_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Frobenius of Q_ℓ raises prime-to-ℓ roots of unity to powers of ℓ.")))))));
}
