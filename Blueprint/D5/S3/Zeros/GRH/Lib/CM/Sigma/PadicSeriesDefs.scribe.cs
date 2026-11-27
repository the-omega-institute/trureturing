using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.Sigma;

internal sealed class PadicSeriesDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Padic Series Defs", H("Padic Series Defs"),
        Blocks(
            Paragraph(Text("Sections of degree m on the curve: division and spanning monomials. Taylor series at 0 of analytic functions: ring laws and injectivity. Ring of integers of C_p and inclusion of integral power series.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/Sigma/PadicSeriesDefs.twistedTranslate_comp_mem"),
                H("twistedTranslate_comp_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If 0 ≠ δ ∈ ℤ[ω], δδ̄ = N and δy ∈ Λ, then z ↦ (U_yθ)(δ̄z) is a section of degree N.")))))));
}
