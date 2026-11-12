using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class TraceOneTensorFactorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TraceOneTensorFactors." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Necessity and full trace-one tensor equivalence", H("Necessity and full trace-one tensor equivalence"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged. The escape audit remains unfinished under linked issue #28398.")),
            Item("complement-root", "complement_root", "Every root has its trace-one complementary root", "All characteristics, including two and repeated roots, are retained."),
            Item("root-product-in-range", "root_product_in_range", "Every root product descends under tensor splitting", "The proof uses the full tensor eigenvector and characteristic polynomial."),
            Item("tensor-splits-iff", "tensor_splits_iff", "Full finite trace-one tensor equivalence", "Every finite family of actual two-dimensional matrices over every field is retained. No semisimplicity or nonzero-determinant premise is added. The necessity proof fixes nonzero roots only in the other factors; the selected factor may have a zero or repeated root.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TraceOneTensorSplitting"))]));
}
