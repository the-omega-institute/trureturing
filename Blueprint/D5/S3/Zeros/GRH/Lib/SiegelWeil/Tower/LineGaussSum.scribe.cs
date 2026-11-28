using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower;

internal sealed class LineGaussSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Gauss Sum", H("Line Gauss Sum"),
        Blocks(
            Paragraph(Text("Finite part of isotropic-line term for standard ramified data is a Gauss sum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LineGaussSum.exists_lineTerm_localDatum"),
                H("exists_lineTerm_localDatum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For adapted A, X there are units κ_β such that, for tame χ, some γ with |γ|² = vol(ϖO) has: the term lineTerm at x = αa, α = scaleIdele E, of the standard datum of s·I′ with I′ = (adaptedFrame r A).I', is κ_β γ χ⁻¹(a)χ(ϖā) times that of s, and 0 unless a is integral off S̄ and a, ϖā are units at S.")))))));
}
