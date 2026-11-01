using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class IntegerPolylineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/IntegerPolyline.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corner lists define the complete integer route, including every endpoint and zero-length segment.",
        H("Exact integer polyline enumeration"), Blocks(
            Paragraph(Text("A point is an integer pair. Each segment has Manhattan length L. Its prefix lists step(a,b,i) for i=0,...,L-1, and the final corner is retained once. For axis-aligned segments this is the same route as retaining the initial point and then appending steps 1,...,L of each segment.")),
            Node("sample", "sample_eq_getD", "Sampling agrees with the full expanded list",
                "For every corner list p and natural index i, the recursive sampler equals the optional i-th element of expand(p), defaulting to (0,0). It searches segment lengths rather than expanding the preceding points. No axis-alignment assumption is needed for this enumeration identity."),
            Node("length", "length_expand", "The expansion has one more point than total segment length",
                "For every nonempty p, expand(p).length = length(p)+1, where length(p) is the sum of Manhattan segment lengths. Zero-length segments add no prefix points."),
            Node("verifier", "expand_eq_verifier", "The two endpoint conventions agree exactly",
                "For every axis-aligned p, expand(p)=verifierExpand(p). The segment endpoint identity joins the left-closed prefixes into the initial-point/right-closed loop. This proves the semantics used to import the actual 1,283 routing corners, including detours and repeated consecutive corners. It supplies no geometric nonintersection or homology assertion."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
