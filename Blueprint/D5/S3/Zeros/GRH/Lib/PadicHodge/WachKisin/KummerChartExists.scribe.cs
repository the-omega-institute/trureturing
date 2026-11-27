using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class KummerChartExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kummer Chart Exists", H("Kummer Chart Exists"),
        Blocks(
            Paragraph(Text("Weil pairs (s, m): products, powers, uniqueness of m. Embedding of W(F_q) into algebraic closure of Q_p via θ; fixers agree. Action of Frobenius and Galois group on A_inf, W(C^♭); Teichmüller roots of unity. Every p-adic field has a Kummer chart from a uniformiser and its root tower.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/KummerChartExists.exists_kummer_chart"),
                H("exists_kummer_chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If j(Γ) is open, there is a chart over Λ = W(F_{p^f}) with ef = [G_p : j(Γ)] such that j(Γ) fixes Λ and θ(z), contains the fixer of θ(S), a p^f-Frobenius and elements with gz = [ε]^l z for all l ≥ 0; e = 1, E = z + p if j(Γ) contains inertia.")))))));
}
