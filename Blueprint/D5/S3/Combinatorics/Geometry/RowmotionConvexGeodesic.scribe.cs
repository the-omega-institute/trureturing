using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionConvexGeodesicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite order-convex sets have guarded toggle paths of Hamming length in every poset.",
        H("Shortest toggle words between finite order-convex sets"), Blocks(
            Paragraph(Text("Let P be an arbitrary partially ordered set. A subset is order-convex when it contains every ambient point between any two of its members. The operation RowmotionEndpointTransport.toggle flips membership at x only when the resulting set is order-convex, and otherwise leaves the set fixed. All intervals and legality tests below use the original order on P.")),
            Describe.Lean(
                DescribeId.Create("rowmotion-convex-geodesic-exists-toggle-word"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/RowmotionConvexGeodesic.exists_toggle_word"),
                H("A word toggling each differing point once"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite order-convex subsets s and t of P, there is a list w with no repetitions whose elements are exactly the symmetric difference of s and t. Its length is the cardinality of that symmetric difference. Starting from s, applying the original guarded toggle successively along w yields t. No finiteness, local finiteness or inhabitance assumption is imposed on P. Empty, disjoint and nested endpoints are included.")),
                    Paragraph(Text("To contract a finite order-convex set A onto an order-convex subset K, choose a point z in A outside K. Finiteness of A supplies a minimal point a of A below z and a maximal point b of A above z. If both a and b belonged to K, convexity of K would force z into K. Thus at least one of these extreme points lies outside K. Deleting a minimal or maximal point preserves ambient order-convexity. Repeating this step gives a deletion word from A to K, with each point of A minus K used once. Every deletion is reversible by the same guarded toggle.")),
                    Paragraph(Text("Apply the contraction to s and t with K equal to their intersection. Follow the deletion word from s to K, then the reverse of the deletion word from t to K. The two lists have disjoint supports, namely s minus t and t minus s, so their concatenation has no repetitions and support s symmetric difference t. This realizes the Hamming lower bound expressed by HereditaryFlip.Metric.walk_lower_bound: each differing coordinate must change at least once along any one-coordinate walk. The contraction argument uses convexity of the retained subset; arbitrary subsets of an order-convex set need not be order-convex."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Statement()
    {
        var p = F.Id("P");
        var s = F.Id("s");
        var t = F.Id("t");
        var w = F.Id("w");
        var setS = Call("coe", s);
        var setT = Call("coe", t);
        var diff = Call("SymmDiff", s, t);
        var step = Seq(Open, F.Id("A"), Comma, Sp, F.Id("x"), Close, Sp, Mapsto, Sp,
            Call("toggle", F.Id("x"), F.Id("A")));
        var conclusion = And(Call("Nodup", w),
            And(Eq(Call("toFinset", w), diff),
                And(Eq(Call("length", w), Call("card", diff)),
                    Eq(Call("foldl", step, setS, w), setT))));
        return All("P", F.Id("Type"),
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Comma, Sp,
                All("s", Call("Finset", p), All("t", Call("Finset", p),
                    Imp(Call("OrdConnected", setS), Imp(Call("OrdConnected", setT),
                        new Formula.Bind(FormulaQuantifier.Exists,
                            FormulaIdentifier.Create("w"), Call("List", p), conclusion)))))));
    }
}
