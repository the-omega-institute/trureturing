using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class DecompositionLocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decomposition Local", H("Decomposition Local"),
        Blocks(
            Paragraph(Text("Places from p-adic embeddings; decomposition group is Galois group of the completion. Decomposition field is local; normalised valuation; index equals e·f in towers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/DecompositionLocal.ramification_in_tower"),
                H("ramification_in_tower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let U ≤ Γ be open, with field L, and A lie over v and w, of ramification index e, residue degree f. Then [Dec(A) : U ∩ Dec(A)] = ef; Ine(A) ≤ U gives e = 1; Dec(A) ≤ U gives q_w = q_v, ord_L = ord_K.")))))));
}
