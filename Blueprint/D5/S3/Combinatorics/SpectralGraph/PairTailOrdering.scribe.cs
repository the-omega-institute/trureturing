using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairTailOrderingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairTailOrdering." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered second-smallest eigenvalue of the entire paired tensor", H("Ordered second-smallest eigenvalue of the entire paired tensor"),
        Blocks(
            Paragraph(Text("Sources: the complete four-prime large-tail, harmonic-tail and unique-tail manuscripts at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All original positive natural parameters are retained, with no ordering between a and b. The sorted spectrum contains all four eigenvalues with multiplicity; the full characteristic polynomial and nonzero tensor eigenpairs identify the actual operator. Original attribution, prerequisites, reports, uncertainties and failed-method boundaries remain unchanged. Necessary tail tests do not assert integrality. General Q3, a6 certification and enumeration reproduction limits stay open. The linked issue #28398 audit remains unfinished; academic approval and publication are separate.")),
            Item("order", "values_antitone", "The complete decreasing spectrum", "The second-smallest value has index two in this four-element decreasing spectrum, with multiplicity."),
            Item("polynomial", "polynomial", "The entire characteristic polynomial", "All four sorted values factor the characteristic polynomial of the full weighted tensor, with no scalar proxy."),
            Item("eigenpair", "eigenpair", "Nonzero full-operator eigenvectors", "Every sorted value is realized by a nonzero vector of the entire paired tensor."),
            Item("bounded", "bounded_window", "The ordered strict bounded-tail window", "For every a>0,b>0,c>=1 the second-smallest eigenvalue lies strictly between a+1 and (a+1)(b+1)."),
            Item("harmonic", "harmonic_window", "The ordered strict harmonic-tail window", "For all a>=1,b>=1,c>b, including the complete original positive natural domain, the second-smallest value lies strictly between a+b+1 and a+1+2bc/(b+c), below a+2b+1."),
            Item("actual", "actual_ordered_value", "Actual graph application for all distinct prime assignments", "For every positive natural a,b,c and every injective prime assignment, the ordered tensor value lifts to the stated actual ideal-intersection graph Laplacian eigenvalue.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairTailSpectrum")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairBinaryPolynomial"))]));
}
