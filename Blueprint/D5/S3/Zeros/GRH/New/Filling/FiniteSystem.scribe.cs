using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class FiniteSystemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite System", H("Finite System"),
        Blocks(
            Paragraph(Text("One-sided Siegel formula at T; top kernel dominates phase sums nearly sharply. Finite places carry a local system with sharp bottom value and frequency bounds.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/FiniteSystem.exists_finite_sieveSystem"),
                H("exists_finite_sieveSystem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let 1/g be integral off T. Some K(g) ≤ Z ≤ K contains k_T whenever k ∈ K reduces into Filling.fixingSet Sg d, and for every compact open subgroup L the normalised forms Level.floorForm, Level.topKernel of Z form a SieveSystem with bottom bound (1 + b⁻⁶)/b^(6|κ||Sg|).")))))));
}
