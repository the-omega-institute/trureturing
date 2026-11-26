using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RibetElementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ribet Element", H("Ribet Element"),
        Blocks(
            Paragraph(Text("Ribet's Hecke element for columns with ties; valuation at the lift within budget.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RibetElement.ribet_columns"),
                H("ribet_columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Ribet's method. Let u_x be IsLabelledColumn, of trace ψ·row + Σ_{e<t} cyc^{−e} with SelmerLengthLe on 𝓧, with places IsPrimeTriangle, and S, 𝒥 as in IsTraceIdeal, e_j(1) = 1. Then x ↦ det Σ_g ω_g(u_x(g) − 1), ω from ribetNormaliser, satisfies IsRibetElement at π with coefficient d, v(chosenGroupOrder³·d) ≤ |r|·rowBudget.")))))));
}
