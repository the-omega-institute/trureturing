using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class CasimirOnPsiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Casimir On Psi", H("Casimir On Psi"),
        Blocks(
            Paragraph(Text("Flensted-Jensen's function is a Casimir eigenfunction with value |λ|²−|ρ|².")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/CasimirOnPsi.casimir_dsCoeffSmooth"),
                H("casimir_dsCoeffSmooth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a parameter λ of gap h, the Casimir operator Ω = Σ E_ab E_ba, acting by right derivatives, satisfies Ωψ_λ = (|λ|² − |ρ|²) ψ_λ.")))))));
}
