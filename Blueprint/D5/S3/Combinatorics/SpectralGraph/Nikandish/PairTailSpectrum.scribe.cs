using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class PairTailSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict full-operator windows and necessary actual-graph tail equations.", H("Strict full-operator windows and necessary actual-graph tail equations."),
        Blocks(
            Paragraph(Text("Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.")),
            Item("bounded", "bounded_eigenpair", "The strict bounded root window", "For every positive real a,b and c>=1 there is a nonzero full tensor eigenpair strictly between a+1 and (a+1)(b+1). The separate PairTailOrdering owner proves the ordered second-smallest window from the complete spectrum."),
            Item("harmonic", "harmonic_eigenpair", "The full harmonic eigenpair window", "For every positive real a and c>b>=1 the same full operator has an eigenpair between a+b+1 and a+1+2bc/(b+c), strictly below a+2b+1. This theorem states a genuine eigenpair; PairTailOrdering separately supplies the full source second-smallest indexing result."),
            Item("candidate", "actual_tail_candidate", "All actual integral graphs force a positive quadratic root", "All positive natural a,b,c and arbitrary distinct prime coordinates retain an integer offset 0<t<(a+1)b, the complete determinant equation and c dividing its positive constant. Passing these tests never proves graph integrality."),
            Item("harmonic-candidate", "actual_harmonic_candidate", "The complete unequal-tail candidate window", "For all positive a,b,c with b<c, actual integrality forces b<t<2b and a negative leading coefficient. There is no ordering between a and b.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailArithmetic"))]));
}
