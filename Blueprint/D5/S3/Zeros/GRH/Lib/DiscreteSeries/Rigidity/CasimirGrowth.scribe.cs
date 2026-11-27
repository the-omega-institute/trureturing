using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity;

internal sealed class CasimirGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Casimir Growth", H("Casimir Growth"),
        Blocks(
            Paragraph(Text("Casimir bounds and linear growth of the Lie algebra action along the filtration. Compact Casimir grows along the filtration, so the lowest K-type occurs once.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/CasimirGrowth.mem_orthogonal_filtration_of_casimirK"),
                H("mem_orthogonal_filtration_of_casimirK"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let λ have gap 500n³+A, IsUnitaryCasimirGe hold, x be K-highest of weight Λ, M_s = GlModule.filtration. If Ω_K a = θa with real θ ≤ |Λ+ρ_c|²−|ρ_c|²+s and a is orthogonal to M_s, then a is orthogonal to every M_t.")))))));
}
