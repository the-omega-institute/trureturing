using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class InterlacingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interlacing", H("Interlacing"),
        Blocks(
            Paragraph(Text("Leading exponent in a row interlaces; leading coefficient is again semi-invariant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Interlacing.degree_rowExpansion_mem_interlacing"),
                H("degree_rowExpansion_mem_interlacing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Interlacing: for f in ∇ of weight l, the leading exponent γ of f in the variables of row x (order PolyRep.columnOrder; γ = 0 if f = 0) satisfies γ(i) ≤ l(c x, i) − l(c x, i+1), truncated at 0, for all i.")))))));
}
