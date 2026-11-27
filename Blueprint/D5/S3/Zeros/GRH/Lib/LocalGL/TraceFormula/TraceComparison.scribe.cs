using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula;

internal sealed class TraceComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace Comparison", H("Trace Comparison"),
        Blocks(
            Paragraph(Text("Equal Hecke traces on unitary groups differing at real places; Selberg principle.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison.exists_trace_eq"),
                H("exists_trace_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let E contain μ_5040, with evenly many infinite places; K a level; each point of hK have irreducible characteristic polynomial at some finite place; B ≥ 16[E:ℚ](n+1)³, H ≥ 500n³+10n⁵. Then ∑⟨b_i, hb_i⟩, b an orthonormal basis of K-fixed forms of type e_l, is the same for all s, V with e_l a cusp kernel of order B, l of gap H.")))))));
}
