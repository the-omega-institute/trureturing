using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeEndpointCausalOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact local and creating-split edges generate the native endpoint order.",
        H("Native endpoint causal order"), Blocks(
        Paragraph(Text("The finite event set and original Call labels are NativeEndpointEventIdeals.events. First chooses the root promotion for alpha birth or root split for beta birth, requiring actual membership. Edge recursively contains exactly a local promotion-before-split edge when both occur, a parent split edge to the first existing local event of either child, and the corresponding shifted edges inside each child. There is no edge into an inactive alpha terminal, and a beta terminal born beta has no event.")),
        Paragraph(Text("Notation and native definitions: "), Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals"), Text(". In particular Bool = {false,true}, Source is the original free binary-tree algebra, Call consists of promote(p) and split(p) at p : List(Bool), Event(b,t) is the subtype of calls in events(b,t), val is its underlying Call, and < is the induced strict prefix/phase order. TransGen(R,c,d) means there is a nonempty finite R-path from c to d; it is not reflexive closure.")),
        Paragraph(Text("For b : Bool, t : Source and e : Call, First(b,t,e) means e = ite(b,promote([]),split([])) and e belongs to events(b,t). For every birth type and all calls c,d, Edge(b,of(a),c,d) is false. For l,r : Source, Edge(b,mul(l,r),c,d) is exactly the disjunction of: b = true, c = promote([]), d = split([]); there exists e : Call with First(false,l,e), c = split([]), d = shift(e,[false]); there exists e : Call with First(true,r,e), c = split([]), d = shift(e,[true]); there exist e,f : Call with c = shift(e,[false]), d = shift(f,[false]), Edge(false,l,e,f); or there exist e,f : Call with c = shift(e,[true]), d = shift(f,[true]), Edge(true,r,e,f). Here a,b range over Bool, c,d over Call, ite is Boolean selection, and shift prefixes the indicated address. This recursive definition retains exactly the original local and creating-split edges.")),
        Describe.Lean(DescribeId.Create("native-endpoint-causal-order"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder.result"),
            H("Exact transitive-closure correspondence"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every birth type, every target and every two members of its endpoint-labelled finite event set, the transitive closure of Edge relates their original Calls exactly when the induced prefix/phase order strictly relates them. This also covers empty and singleton event sets. The result identifies the order used by native execution adequacy with the exact causal order defined in Atomic Generation Acquisition AA17.2; it is consumed for every promised comb by NativePromiseCausalBoundary.result.")),
            Paragraph(Text("Every generating edge strictly increases the prefix/phase order. Conversely, structural induction finds the first local event before any event in a nonempty child. A parent split reaches that first event directly and then follows the child induction. A root promotion first reaches the root split. Events in one child lift that child's generating path; distinct children cannot be related by prefix ancestry. Thus every strict comparison has an actual path of the specified local edges. Antisymmetry of the existing partial order excludes directed cycles.")),
            Paragraph(Text("The correspondence proves source-specific causal structure, with no execution, reachability, rational clock, chosen serial order or probability-law premise. Full seven/eight laws remain outside this module."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Open, body, Close);
    private static Formula Statement()
    {
        var b = V("b"); var t = V("t"); var c = V("c"); var d = V("d");
        var events = C("Event", b, t);
        return Q("b", C("Bool"), Q("t", C("Source"), Q("c", events, Q("d", events,
            Seq(C("TransGen", C("Edge", b, t), C("val", c), C("val", d)),
                Sp, Iff, Sp, c, Sp, Lt, Sp, d)))));
    }
}
