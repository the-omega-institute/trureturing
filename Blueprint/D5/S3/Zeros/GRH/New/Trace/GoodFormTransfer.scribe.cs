using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Trace;

internal sealed class GoodFormTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Good Form Transfer", H("Good Form Transfer"),
        Blocks(
            Paragraph(Text("Good forms on different unitary groups have equal traces. On the unitary groups U(Y₀) of the rows and U(W_j), the sources of the single lifts, a Hecke eigensystem admits at most one primitive cuspidal type at a given prime above g, so good forms on these groups have equal Hecke traces, determinants, dimension and eigensystems. Transfer between inner forms for representations supercuspidal at two split places, multiplicity one and unicity of depth-zero types are known, and equal Hecke traces follow by a simple trace formula. Related work: Harris–Labesse, Conditional base change for unitary groups, 2004; Labesse, Changement de base CM et séries discrètes, 2011; Latham, Unicity of types for depth-zero supercuspidal representations, 2017.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Trace/GoodFormTransfer.finrank_rows_eq_finrank_goodForms"),
                H("finrank_rows_eq_finrank_goodForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 1 ≤ j ≤ m, the space of rows (good forms on Y₀) has the same complex dimension as the space of good forms on W_j.")))))));
}
