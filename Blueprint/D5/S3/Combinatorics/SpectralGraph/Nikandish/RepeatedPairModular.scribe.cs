using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class RepeatedPairModularDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModular." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full arbitrary-prime modular obstruction on actual ideal graphs", H("Full arbitrary-prime modular obstruction on actual ideal graphs"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged.")),
            Item("kernel-tensor", "kernel_tensor", "Every support subset is a tensor coordinate", "The complete disjointness kernel is reindexed by the entire function space."),
            Item("actual-factor-splits", "actual_factor_splits", "All field characteristics annihilating a+1", "Actual graph integrality supplies the full characteristic polynomial before reduction."),
            Item("actual-prime-splits", "actual_prime_splits", "Every prime divisor and every tail exponent", "For every finite tail index and every prime dividing a+1, all trace-one tail quadratics split. There is no tail-order assumption. Passing is necessary only.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TraceOneTensorFactors"))]));
}
