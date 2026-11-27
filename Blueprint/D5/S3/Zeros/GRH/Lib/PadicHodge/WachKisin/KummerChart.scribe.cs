using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class KummerChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kummer Chart", H("Kummer Chart"),
        Blocks(
            Paragraph(Text("Regularity of B_max: invariant fractions lie in W[1/p], via a Kummer chart. Kisin's ring W[[z]] in A_inf, primes φ^a E, Galois congruences, different bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/KummerChart.zTau_mul_E_dvd_smul_sub"),
                H("zTau_mul_E_dvd_smul_sub"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a Kummer chart, g in its group Γ' and s ∈ S, the element zτE divides gs − s in A_inf.")))))));
}
