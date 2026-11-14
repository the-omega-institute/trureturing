using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class TraceOneTensorSplittingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TraceOneTensorSplitting." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sufficiency of factor splitting for the full trace-one tensor", H("Sufficiency of factor splitting for the full trace-one tensor"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged.")),
            Item("tensor-eigenpair", "tensor_eigenpair", "Products of actual nonzero factor eigenvectors", "All tensor coordinates occur and the resulting eigenvector is proved nonzero."),
            Item("triangular-conjugacy", "triangular_conjugacy", "Trace-one two-dimensional triangularization", "Repeated roots and zero roots are allowed over every field."),
            Item("splits-of-factors", "splits_of_factors", "All split factors give a split tensor characteristic polynomial", "The finite tensor of invertible triangularizations and a linear extension of the coordinate order retain all diagonal multiplicities.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairIntegralPolynomial"))]));
}
