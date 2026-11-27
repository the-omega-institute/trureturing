using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class ThetaKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Kernel", H("Theta Kernel"),
        Blocks(
            Paragraph(Text("A_inf: kernel of θ, divisibility by μ and τ, φ-equations, completeness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/ThetaKernel.isAdicComplete_span_pair"),
                H("isAdicComplete_span_pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a and c are non-units of A_inf, then A_inf is complete and separated for the adic topology of the ideal (a, c).")))))));
}
