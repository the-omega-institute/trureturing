using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class BijectiveComparisonsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bijective Comparisons", H("Bijective Comparisons"),
        Blocks(
            Paragraph(Text("Covers by sums of representables; Ext commutes with products of coefficient functors. A pointwise bijection of functors induces isomorphisms on cohomology. Bijectivity criteria for comparison maps: representables, Čech descent, fibrewise and universal points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/BijectiveComparisons.isBijective_subfunctor"),
                H("isBijective_subfunctor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If u: Y' → Y∘φ has universal points (Comparison.HasUnivPoints), then for every subfunctor U of Y the comparison is bijective in all degrees along the restricted map u⁻¹(U∘φ) → U∘φ.")))))));
}
