using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridPathsdocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact numeric-word and all-length full-state counting", H("Exact numeric-word and all-length full-state counting"), Blocks(
            N("runWeight", "runWeight", "An appended-mask word receives the product of its accepted transition indicators and its full terminal weight. It is always zero or one.", DescribeRole.Definition),
            N("sum_runWeight", "sum runWeight", "For every suffix length k and every full state s, summing runWeight k s over every Fin k → Fin 8 word is exactly fullOrbit k s. The first-mask function equivalence supplies the induction.", DescribeRole.Theorem),
            N("fullStep_eq_mulVec", "fullStep eq mulVec", "For every full integer vector v, fullStep v equals transition.mulVec v. Injectivity of append identifies accepted masks with admitted unit-weight successors.", DescribeRole.Theorem),
            N("fullOrbit_matrix", "fullOrbit matrix", "For every natural k, fullOrbit k is the action of transition raised to k on the terminal vector. The proof applies the pinned matrix multiplication action laws.", DescribeRole.Theorem),
            N("trace", "trace", "The start and each successive appended mask determine the entire ordered full-state path.", DescribeRole.Definition),
            N("trace_unique", "trace unique", "For every k, state s, suffix word w and state path p with the prescribed start and append equations, p equals trace k s w. No witness choices or symmetry quotients enter the path.", DescribeRole.Theorem),
            N("expanded", "expanded", "Signed coordinates −2,−1,0,1 read the four history columns; the supplied suffix supplies successive real masks, and subsequent columns are absent.", DescribeRole.Definition),
            N("expandedWindow", "expandedWindow", "The five symbols centred at a nonnegative coordinate are read from the history-and-suffix stream.", DescribeRole.Definition),
            N("runWeight_iff_tests", "runWeight iff tests", "For every k, full state s and suffix w, runWeight k s w equals one exactly when every centre in Fin(k+2) satisfies the corresponding Local window test. The base k=0 is precisely the two terminal checks.", DescribeRole.Theorem),
            N("start", "start", "The two labelled real masks a,b encode the full start state 8*a+b in the first block.", DescribeRole.Definition),
            N("accepted_cons_iff", "accepted cons iff", "For every suffix length k, masks a,b and suffix w, the concatenated numeric word belongs to acceptedWords(k+2) exactly when its unique run from start a b has weight one.", DescribeRole.Theorem),
            N("actualCount_fullOrbit", "actualCount fullOrbit", "For every natural k, the actual inclusion-minimal dominating subset count of the ordinary open grid of width k+2, cast to the integers, equals the sum of fullOrbit k over all 64 starts. This includes width two with no transitions.", DescribeRole.Theorem),
            Paragraph(Text("This is internal Stage A work. The unchanged whole actual-subset generating-series endpoint requires every counting and quotient interface to be compiled; no resolution or admission follows from a partial interface."))), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bp-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
