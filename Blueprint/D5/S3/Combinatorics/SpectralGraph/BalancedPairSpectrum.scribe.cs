using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class BalancedPairSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/BalancedPairSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced intervals and the separate general upper-four bound.", H("Balanced intervals and the separate general upper-four bound."),
        Blocks(
            Paragraph(Text("Source: four-prime-single-pair-balanced, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("upper", "repeated_minimum_low", "The general repeated-minimum upper-four bound", "For every real a>=5 and b,c>=a, with no ordering between tails, the empty/full principal minor produces an eigenpair in (1,4). This bound alone proves no nonintegrality in that larger region."),
            Item("balanced", "balanced_eigenpair", "The full real balanced interval", "Every a<=b<=c<=2a-6 has a genuine full tensor eigenpair in (3,4); the hypotheses imply a>=6."),
            Item("actual", "actual_balanced_interval", "Actual graph interval including both tail boundaries", "All natural balanced parameters and arbitrary distinct primes have an actual ideal-graph eigenvalue in (V-3,V-2)."),
            Item("integrality", "actual_nonintegral", "Whole balanced family nonintegrality", "The strict unit interval proves nonintegrality throughout the original domain, with no finite exponent base. The neighboring offset-five interval is not asserted."),
            Item("minimum", "minimum_window", "The genuine smallest full-operator interval", "The exact minimum compares against every nonzero real eigenpair of the full weighted tensor and lies in (3,4) on the entire real balanced domain.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/BalancedPairDeterminant"))]));
}
