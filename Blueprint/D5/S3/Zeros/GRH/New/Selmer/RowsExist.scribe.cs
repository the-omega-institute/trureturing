using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RowsExistDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rows Exist", H("Rows Exist"),
        Blocks(
            Paragraph(Text("A twist-free row gives traces of lifts; every good eigensystem has a row.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RowsExist.exists_hasRow_auxPair"),
                H("exists_hasRow_auxPair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the system p of Hecke eigenvalues occurs in a nonzero good form on W_m, then for 1 ≤ j ≤ m some T is a row for the untwisted j-th auxiliary pair and p, serving all twists (HasRow).")))))));
}
