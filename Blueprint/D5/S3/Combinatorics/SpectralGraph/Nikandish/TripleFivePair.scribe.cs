using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class TripleFivePairDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TripleFivePair." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete twenty-nine-offset triple-five family.", H("The complete twenty-nine-offset triple-five family."),
        Blocks(
            Paragraph(Text("Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.")),
            Item("identity", "quadratic", "The entire fixed-pair quadratic identity", "The three exact coefficient formulas hold for every integer offset and algebraic tail, before positive-domain restrictions."),
            Item("candidates", "integer_candidate", "All twenty-nine original offsets", "Seven complete nonsquare brackets, the factored fifth row, the entire positive coefficient interval 9 through 28, and the negative last discriminant leave only t=c=5. The tail c stays unbounded."),
            Item("factor", "diagonal_factor", "The complete exceptional quartic factorization", "At the sole remaining candidate the quartic factors as (x-11) times the original cubic, with all coefficients retained."),
            Item("cubic", "diagonal_eigenpair", "The genuine exceptional cubic eigenpair", "The full tensor has a nonzero eigenpair in (3,4). This supplies the source witness at the surviving fifth tail, rather than treating the necessary candidate as integral."),
            Item("actual", "actual_nonintegral", "Every positive free triple-five tail", "The actual graph is nonintegral for every positive c, including c<5 and c=5, uniformly in all four distinct prime coordinates. The historical source control/reproduction and general Q3 boundaries remain unchanged.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum"))]));
}
