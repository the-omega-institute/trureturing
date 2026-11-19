using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class PairTailSeparationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full paired-tensor middle-root separation and actual graph applications", H("Full paired-tensor middle-root separation and actual graph applications"),
        Blocks(
            Paragraph(Text("Sources: the entire original large-tail and harmonic-tail manuscripts, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The harmonic source assumes all positive natural a,b,c with b<c and no ordering between a and b. The full four-value spectrum retains multiplicity. The lower ordered value is the second-smallest and the next is the third-smallest. Both lift through the existing actual ideal-intersection graph application for every injective prime assignment. Original attribution, prerequisites, source reports, failed methods, uncertainties and rights boundaries remain unchanged. Root conditions and candidate tests do not establish integral spectrum. General Q3, a6 certification and finite-enumeration reproduction limits remain open.")),
            Item("bounded", "bounded_separation", "Full bounded middle-root separation", "For every real a>0,b>0,c>=1 the bounded endpoint (a+1)(b+1) lies strictly between the ordered second-smallest and third-smallest roots; the second-smallest also exceeds a+1."),
            Item("harmonic", "harmonic_separation", "Entire original harmonic separation and endpoint chain", "For every real a>=1,b>=1,c>b, the full chain a+b+1 < kappa2 < a+1+2bc/(b+c) < kappa3 holds, with the strict endpoint bound a+1+2bc/(b+c) < a+2b+1."),
            Item("spectrum", "actual_spectrum", "Every ordered tensor value lifts to the actual graph", "For every positive natural a,b,c and every distinct-prime assignment, every one of the four sorted values yields the stated actual graph Laplacian eigenvalue V+1-kappa."),
            Item("application", "actual_harmonic_separation", "Both middle values are actual graph eigenvalues", "The original complete harmonic chain and both genuine graph eigenvalue applications hold together over all positive natural parameters with b<c, without an order restriction between a and b.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailOrdering"))]));
}
