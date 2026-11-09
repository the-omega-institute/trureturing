using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class DoublePairCubicDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/DoublePairCubic." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full invariant cubic and endpoint reductions.", H("The full invariant cubic and endpoint reductions."),
        Blocks(
            Paragraph(Text("Source: four-prime-double-pair-completion, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("action", "cubic_action", "The complete invariant-subspace action", "The second swap gives a three-dimensional genuine restriction of the full tensor, not a principal-submatrix spectral proxy."),
            Item("factor", "factorization", "Full scalar times cubic factorization", "The scalar eigenvalue a+b+1 and the invariant cubic give the entire four-dimensional characteristic determinant."),
            Item("two-bracket", "two_bracket", "The full unbounded exponent-root bracket at two", "For every real a at least two, the endpoint-two exponent polynomial is negative at 2a squared minus two and positive at 2a squared minus one."),
            Item("three-bracket", "three_bracket", "All eight fixed brackets and the infinite tail", "The exact source rows at a=5 through 12 and the symbolic a at least 13 bracket are all retained. They are complete finite arithmetic for the unbounded argument, not an exponent scan."),
            Item("two", "two_nonzero", "The entire integer-tail endpoint-two exclusion", "Every natural a at least two and positive integer tail avoids the endpoint-two exponent root."),
            Item("three", "three_nonzero", "The entire ordered endpoint-three exclusion", "Every natural a at least two and b at least a avoids endpoint three, including the a=2 positive polynomial and the a=3,4 smaller-root boundaries.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
