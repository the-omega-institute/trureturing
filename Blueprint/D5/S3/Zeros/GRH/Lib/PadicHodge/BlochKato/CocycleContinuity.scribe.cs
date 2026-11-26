using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.BlochKato;

internal sealed class CocycleContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cocycle Continuity", H("Cocycle Continuity"),
        Blocks(
            Paragraph(Text("Filtered de Rham frame; extensions by crystalline cocycles are admissible; such cocycles are continuous.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/CocycleContinuity.eventually_eq_pow_smul"),
                H("eventually_eq_pow_smul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let T be finite free over Z_p and potentially crystalline. For c in Z_f(T) and every m, the value c(g) lies in p^m T for all g with j(g) near 1.")))))));
}
