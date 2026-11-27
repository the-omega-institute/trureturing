using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class TailBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tail Bounds", H("Tail Bounds"),
        Blocks(
            Paragraph(Text("Explicit Lipschitz bound for the coefficient; crude bound for degree times tail integrals.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/TailBounds.integral_tail_le"),
                H("integral_tail_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For l=2λ of gap 500n³+B with all |l_a| ≤ L and a natural number c > 8n², the function deg_λ·(2/‖g‖)^c is integrable on U(diag ε), with integral at most 8(2000(n+L+1)⁶)^{2n²}·2^c.")))))));
}
