using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Comparison;

internal sealed class CrystallineLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Limit", H("Crystalline Limit"),
        Blocks(
            Paragraph(Text("Dwork's trick: after Frobenius the frame is constant basis times unit over A_max. Uniform denominator for the integral crystalline comparison over A_max, independent of rank. Limit of crystalline representations of bounded weights is crystalline (Liu), group-ring form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit.isCrystalline_of_trace_limit"),
                H("isCrystalline_of_trace_limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Limits of crystalline representations. G compact, toGp : Δ → Gp p (from OverGp) of open image, w: Δ → Z_p[G] multiplicative, R continuous with IsTraceNondeg; X finite families of continuous representations, crystalline along w with jumps in [0, h]. If ‖tr R‖ ≤ ε on the kernel in Z_p[G] of some family, for each ε > 0, then R∘w is crystalline.")))))));
}
