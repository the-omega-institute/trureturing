using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairTailArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tail equations, positive roots and contiguous offset cutoffs.", H("Exact tail equations, positive roots and contiguous offset cutoffs."),
        Blocks(
            Paragraph(Text("Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.")),
            Item("determinant", "determinant", "The entire unrestricted quadratic identity", "The determinant identity holds in every commutative ring before restrictions on any parameter. The algebraic constant at c=0 is not a positive ideal exponent."),
            Item("constant", "H_positive", "A nonzero constant throughout every candidate window", "Every positive ordered-ring a,b,t with t<(a+1)b has the exact positive source constant. This proves the integer candidate polynomial is nonzero."),
            Item("linear", "B_positive", "All thirty-four positive coefficient terms", "All integer offsets b<t<2b and a>=1 retain the complete source positive expansion, with no bound on either exponent."),
            Item("unique", "positive_root_unique", "At most one positive integer root at each harmonic offset", "Two positive integer tails at the same offset coincide. A nonnegative leading coefficient excludes all positive roots."),
            Item("real-root", "positive_real_root", "The exact unique positive real root", "When the leading coefficient is negative, the original positive square-root formula gives the unique positive real root of the full determinant. Integrality, divisibility, c>b and the other graph eigenvalues remain independent necessary checks."),
            Item("cutoff", "leading_cutoff", "The unique continuous leading-coefficient cutoff", "For every real a>0,b>=1 there is a cutoff tau strictly between b and 2b. At every t>=b the leading coefficient is negative exactly when t<tau. The integer source domain is included, with no claim about excluded smaller real b.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
