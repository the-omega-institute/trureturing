using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionEndpointTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete reverse extension transports minimal ceiling endpoints to maximal floor endpoints.",
        H("Endpoint transport along the literal toggle trace"),
        Blocks(
            Paragraph(Text("Let P be a partially ordered set and let e be an equivalence from Fin N to P. The equivalence enumerates every point exactly once. Write index(e,x) for the natural value of e's inverse at x. ReverseExtension means that a strictly larger point has a smaller index. All orders and extrema below refer to the given partial order, including when two comparable points share a coordinate in a product order.")),
            Definition("ReverseExtension", "A complete reverse linear extension", "The enumeration visits every strictly larger point before a strictly smaller point. Completeness and uniqueness come from the equivalence, rather than from this order condition alone."),
            Definition("toggle", "The interval-closed toggle", "Toggle x in S by taking its symmetric difference with the singleton x when that candidate is order-convex; otherwise retain S. Order-convexity means that every point between two included points is included."),
            Definition("trace", "The successive literal states", "Start with trace(e,I,0)=I. At step k below N, toggle the point e(k). At and after N the state stays fixed. In the displayed recurrence e(k) denotes evaluation at the element of Fin N with natural value k, under the condition k<N."),
            Theorem("endpoint_transport", "Minimal ceiling endpoints become maximal floor endpoints", "Let I be order-convex, let m be globally minimal in I, and let c be globally minimal in the non-strict upper closure of I minus I, with m strictly below c. For the actual final state J=trace(e,I,N), c is globally maximal in J, and m is globally maximal in the non-strict lower closure of J minus J. The claim holds for every complete reverse extension and every finite poset, including all finite rectangles."),
            Paragraph(Text("At a point's visit, all smaller points retain their initial membership and all larger points have their final membership. An initial included point below an initial hole prevents insertion of any point strictly above that hole. Applying this to m<c excludes every final point above c. Minimality of c makes its insertion order-convex. Minimality of m permits its removal. Finally, any point strictly between m and a final included point either was initially present and cannot be removed, or was initially absent and would have blocked that final point's insertion. This proves maximality of m in the final floor.")))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rowmotion-endpoint-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(F.Id(name), Open, Seq(arguments.SelectMany((value, index) =>
            index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And,
            Seq(Open, right, Close));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies,
            Seq(Open, right, Close));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Iff,
            Seq(Open, right, Close));
    private static Formula Difference(Formula left, Formula right) =>
        Seq(left, Sp, Setminus, Sp, right);

    private static Formula Statement(string name)
    {
        var p = F.Id("P");
        var n = F.Id("N");
        var e = F.Id("e");
        var i = F.Id("I");
        var s = F.Id("S");
        var x = F.Id("x");
        var y = F.Id("y");
        var m = F.Id("m");
        var c = F.Id("c");
        var k = F.Id("k");
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var type = new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
        var set = Call("Set", p);
        var equiv = Call("Equiv", Call("Fin", n), p);
        var successor = Seq(k, Sp, Plus, Sp, D(1));
        var state = Call("trace", e, i, k);
        var next = Call("trace", e, i, successor);
        var final = Call("trace", e, i, n);
        var flip = Call("SymmDiff", s, Seq(OpenBrace, x, CloseBrace));
        Formula body;
        if (name == "toggle")
        {
            body = All("x", p, All("S", set,
                Equal(Call("toggle", x, s),
                    Call("If", Call("OrdConnected", flip), flip, s))));
        }
        else
        {
            body = name switch
            {
                "ReverseExtension" => Iff(Call("ReverseExtension", e),
                    All("x", p, All("y", p,
                        Imp(Rel(x, FormulaRelationOperator.LessThan, y),
                            Rel(Call("index", e, y), FormulaRelationOperator.LessThan,
                                Call("index", e, x)))))),
                "trace" => All("I", set,
                    And(Equal(Call("trace", e, i, D(0)), i),
                        All("k", nat,
                            And(Imp(Rel(k, FormulaRelationOperator.LessThan, n),
                                    Equal(next, Call("toggle", Call("eval", e, k), state))),
                                Imp(Rel(n, FormulaRelationOperator.LessThanOrEqual, k),
                                    Equal(next, state)))))),
                "endpoint_transport" => All("I", set, All("m", p, All("c", p,
                    Imp(Call("ReverseExtension", e),
                        Imp(Call("OrdConnected", i),
                            Imp(Call("Minimal", i, m),
                                Imp(Call("Minimal", Difference(Call("upperClosure", i), i), c),
                                    Imp(Rel(m, FormulaRelationOperator.LessThan, c),
                                        And(Call("Maximal", final, c),
                                            Call("Maximal", Difference(Call("lowerClosure", final), final), m)))))))))),
                _ => throw new ArgumentOutOfRangeException(nameof(name))
            };
            body = All("N", nat, All("e", equiv, body));
        }
        return Disp(All("P", type,
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Sp, body)));
    }
}
