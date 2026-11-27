using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class CokernelKillersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cokernel Killers", H("Cokernel Killers"),
        Blocks(
            Paragraph(Text("Low and far weight windows, gap condition, sum of valuations over two intervals. Annihilators p^κ E^s of cokernels of Kisin modules on crystalline extensions. S ⊂ A_inf is the power series ring of the Kummer chart, z its variable, E = z^e·(unit) + p; a letter is a unit of the field with p^f elements (Lift.KummerChart.Letter).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/CokernelKillers.killsCokernel_of_isUnramified"),
                H("killsCokernel_of_isUnramified"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Unramified chart, p ≥ 5: if all allowed jumps are ≤ (p − 3)(s + t), then p^s E^t times the part of A_inf ⊗ C at the letter i lifts to the extension's module of standard exponents of level 0.")))))));
}
