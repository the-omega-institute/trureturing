using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class MovedVacuumCombDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moved Vacuum Comb", H("Moved Vacuum Comb"),
        Blocks(
            Paragraph(Text("A moved translate of the vacuum is an admissible average of vacuum translates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/MovedVacuumComb.isAdmissibleComb_weil_vacElem"),
                H("isAdmissibleComb_weil_vacElem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let g be finite, cC = Δ_f(g), and g(x + Ô^n) ⊂ A. If dc/|Δ_f(g)|² is integral away from q and, under p, all |σc| ≤ 1, then ω(g)ϱ_f(x)vac is an admissible combination of the Cϱ_f(z)vac, z ∈ A, of denominator d and size 1.")))))));
}
