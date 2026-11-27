using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic;

internal sealed class HolomorphicChamberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic Chamber", H("Holomorphic Chamber"),
        Blocks(
            Paragraph(Text("Discrete series coefficient equals a product of minors in the holomorphic chamber.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber.dsCoeff_eq_holMinors"),
                H("dsCoeff_eq_holMinors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Holomorphic discrete series: order o with signs +1 first, w K-dominant, w_i+γ ≤ w_j for ε_i = 1, ε_j = −1, γ > 500n³+A+n+1, λ_i = w_i + (n+1)/2 − i with i the rank in o. Then λ has gap 500n³+A and ψ_λ = holMinors ε w on U(diag ε).")))))));
}
