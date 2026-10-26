using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralMinimalDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-private witnesses and the exact labelled one-apex family in a trapezohedral graph.",
        H("Trapezohedral minimal domination"),
        Blocks(
            Paragraph(Text("The graph has distinct labels alpha, beta, a(i), b(i), with cyclic indices in Fin n. Its only edges are alpha--a(i), beta--b(i), a(i)--b(i), and b(i)--a(i+1). The apices are nonadjacent. OEIS A381190, revision 16, asks for the ordinary generating function of connected minimal dominating subsets for every n at least three. Minimal means inclusion minimal among all dominating subsets, independently of connectivity; actual labelled subsets are counted without a symmetry quotient.")),
            Node("graph", "The labelled graph", "graph",
                "Four edge families, with successor given by the canonical cyclic permutation of Fin n.", DescribeRole.Definition),
            Node("minimal-domination", "Inclusion minimality", "MinimalDominating",
                "A closed dominating set S such that any dominating subset T of S contains all of S. No connectivity condition is imposed on T.", DescribeRole.Definition),
            Node("closed-private", "Closed-private witness", "ClosedPrivate",
                "A vertex w is dominated by s and by no other selected vertex. The witness w=s is allowed.", DescribeRole.Definition),
            Node("private-characterization", "Closed-private characterization", "minimalDominating_iff_private",
                "Minimal domination is equivalent to domination together with a closed-private witness for each selected vertex. The statement holds for arbitrary vertex types, and its proof compares against all subsets.", DescribeRole.Theorem),
            Node("proper-subsets", "All proper subsets", "minimalDominating_iff_proper",
                "The subset formulation is equivalent to failure of domination for every proper subset, without restricting those subsets to be connected.", DescribeRole.Theorem),
            Node("actual-count", "The source counting sequence", "actualCount",
                "The cardinality of the filtered powerset of the full labelled vertex set when n>=3, and zero for n<3. Auxiliary paths of small orders are not trapezohedral graph cases.", DescribeRole.Definition),
            Node("one-apex", "Exact fixed-tag correspondence", "alphaSet_admissible_iff",
                "For n>=3, S={alpha,b(j)} together with selected a-labels C is admissible exactly when C is a minimal cover of every cyclic edge except j, C contains an endpoint of the deleted edge, and C omits an interior label. The first condition governs domination and the selected a-vertices' privacy; the endpoint condition governs induced connectivity; the interior omission is the apex's private witness. Beta is the private witness for b(j). This is a fixed-tag equivalence and does not assert that all admissible sets have such a tag, identify the cut cycle with an ordered path, or establish the original generating series.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
