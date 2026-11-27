using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class DeepFormCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deep Form Cost", H("Deep Form Cost"),
        Blocks(
            Paragraph(Text("A form deep in every frame has a monomial of large cost.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/DeepFormCost.exists_le_weight_of_mem_deepForms"),
                H("exists_le_weight_of_mem_deepForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let char K = p, 2r ≤ k, 2r < N. A non-zero F in TwistingData.deepForms has a monomial of weight ≥ τ, deep variables (b,s) weighing P^{−2r} if b ≥ 2r (b from 0), 1/P otherwise, the others 0.")))))));
}
