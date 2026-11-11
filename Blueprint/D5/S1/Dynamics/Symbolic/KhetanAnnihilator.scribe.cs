using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanAnnihilatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Supplier =
        LibraryNoteRef.Create("D5/L/Dynamics/ho2026nivat");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic periodizer bridge for finite-alphabet lattice configurations.",
        H("KhetanAnnihilator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-product-differences"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanAnnihilator.exists_integer_product_differences"),
                H("Integer product of differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Supplier),
                Blocks(Paragraph(Text("The supplier applies to the original finite-range integer configuration and returns a nonempty list of nonzero lattice directions. It asserts neither separation nor independence of those directions."))),
                DescribeRole.Theorem))));
}
