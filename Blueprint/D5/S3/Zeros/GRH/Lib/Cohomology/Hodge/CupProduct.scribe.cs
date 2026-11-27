using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class CupProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cup Product", H("Cup Product"),
        Blocks(
            Paragraph(Text("Tensor product of functors, total Ext with Yoneda composition, cup product and naturality.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/CupProduct.pull_cup"),
                H("pull_cup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The external product is natural in the site: if a comparison (φ,β) from F to F' carries the pairing μ on F to μ' on F', its pull-back along η: Θ' → Θ∘φ sends x × y to the product of the pull-backs (F, F', N flat).")))))));
}
