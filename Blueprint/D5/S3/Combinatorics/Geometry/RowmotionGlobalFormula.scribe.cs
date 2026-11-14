using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionGlobalFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lafreniere2025intervalclosed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The interval-closed toggle sweep on a finite poset has an explicit formula in its initial ceiling and lower boundary.",
        H("The global formula for interval-closed rowmotion"),
        Blocks(
            Paragraph(Text("Let P be an arbitrary partially ordered set. An equivalence e from Fin N to P enumerates all its points once, and a reverse extension visits every strictly larger point before every strictly smaller point. Start from an order-convex set I. The toggle at a point replaces the current state by its symmetric difference with that singleton exactly when the replacement is order-convex. The trace is the literal sequence of these toggles, with initial state I.")),
            Paragraph(Text("Theorem 1.1 and its proof in Lafreniere, Lewis, McNicholas, Striker and Welch, Interval-closed set rowmotion and homomesy on products of two chains, arXiv:2505.04000v1, give this finite-poset image formula. The ceiling, lower boundary and incomparable region below express the sets in that formula. The statement here uses an arbitrary universe and includes empty posets and empty boundaries.")),
            Paragraph(Text("The Lean proof adapts the set-side and local-flip arguments from Columbus Labs, interval-closed-rowmotion, as identified in the Lean source. That source retains the adaptation attribution and MIT license separately from the mathematical attribution to Lafreniere, Lewis, McNicholas, Striker and Welch.")),
            Node("ceiling", "The upper boundary", DescribeRole.Definition,
                "The ceiling C consists of the minimal elements of the upper closure of I outside I. All closures and minimality statements use the given partial order. The upper closure is non-strict, so it includes I itself."),
            Node("lowerBoundary", "The eligible initial minima", DescribeRole.Definition,
                "The lower boundary H is the intersection of the minimal elements of I with the lower closure of C. A minimum is eligible exactly when it lies below at least one ceiling point."),
            Node("incomparable", "The full incomparable region", DescribeRole.Definition,
                "A point belongs to the incomparable region of C precisely when, for every c in C, neither the point is at most c nor c is at most the point. If C is empty, this region is the whole poset."),
            Node("formula", "The proposed image", DescribeRole.Definition,
                "Take the union of the incomparable region outside I and the lower closure of C outside the lower closure of H. Both differences are ordinary set differences. The expression depends only on I and the order, and does not use a toggle trace."),
            Node("trace_eq_formula", "Every reverse extension gives the explicit image", DescribeRole.Theorem,
                "For every natural N, every equivalence e from Fin N to P satisfying the reverse-extension condition, and every order-convex initial I, the final literal state trace(e,I,N) equals formula(I). There are no nonemptiness assumptions on P, I, C or H, and the theorem includes N=0."),
            Paragraph(Text("The ceiling is an antichain. Finiteness supplies a minimal initial hole below every point of the upper closure outside I. Conversely, order-convexity shows that every point above a ceiling point is outside I. Thus the upper closure of C is exactly the upper closure of I outside I. The lower and upper closures of the antichain meet precisely in C.")),
            Paragraph(Text("The proposed image is order-convex. No point in it lies below an eligible initial minimum. Between two proposed-image points, a point in the lower closure of C therefore belongs to the second difference. A point outside that lower closure has no ceiling point below it, because the larger endpoint lies in the incomparable region. It also cannot belong to I: otherwise the larger endpoint would be above an initial point but outside I, and hence above a ceiling point. This puts it in the first difference.")),
            Paragraph(Text("Every ceiling point belongs to the proposed image, and every minimal point of I is excluded. A point initially in I belongs to the proposed image exactly when an initially included point lies strictly below it and a proposed-image point lies strictly above it. For an initially absent point, membership is equivalent to two no-hole conditions: all intervals up from initially included lower endpoints are filled in I below the point, and all intervals down from proposed-image upper endpoints are filled in the proposed image above the point.")),
            Paragraph(Text("To connect these conditions to the actual dynamics, consider an order-convex intermediate state at the visit of x. Suppose its membership agrees with I at x and strictly below x, and with the proposed image strictly above x. If x is initially present, deletion fails exactly when two retained endpoints force x to remain between them. If x is initially absent, insertion is legal exactly when both no-hole conditions hold. Consequently, toggling x makes its membership equal to the proposed image. Membership at every other point stays fixed.")),
            Paragraph(Text("Induction over the enumeration now shows that processed points have their proposed-image membership and unprocessed points have their initial membership. Reverse order ensures the lower and upper agreements needed at each visit. Each literal toggle preserves order-convexity by its definition. At N every point has been processed, giving the asserted equality. For an empty ceiling the formula reduces to the complement of I; for an empty poset the same induction has no visits. Neither case requires a separate existence assumption.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(
            DescribeId.Create("rowmotion-global-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(F.Id(name), Open, Seq(arguments.SelectMany((value, index) =>
            index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Mem(Formula x, Formula s) => Rel(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Difference(Formula a, Formula b) =>
        Seq(Open, a, Sp, Setminus, Sp, b, Close);

    private static Formula Statement(string name)
    {
        var p = F.Id("P");
        var i = F.Id("I");
        var x = F.Id("x");
        var c = F.Id("c");
        var set = Call("Set", p);
        var ceiling = Call("ceiling", i);
        var boundary = Call("lowerBoundary", i);
        Formula body = name switch
        {
            "ceiling" => All("I", set, All("x", p,
                Iff(Mem(x, ceiling), Call("Minimal", Difference(Call("upperClosure", i), i), x)))),
            "lowerBoundary" => All("I", set, All("x", p,
                Iff(Mem(x, boundary), And(Call("Minimal", i, x), Mem(x, Call("lowerClosure", ceiling)))))),
            "incomparable" => All("C", set, All("x", p,
                Iff(Mem(x, Call("incomparable", F.Id("C"))), All("c", p,
                    Imp(Mem(c, F.Id("C")), And(
                        new Formula.Not(Rel(x, FormulaRelationOperator.LessThanOrEqual, c)),
                        new Formula.Not(Rel(c, FormulaRelationOperator.LessThanOrEqual, x)))))))),
            "formula" => All("I", set, Rel(Call("formula", i), FormulaRelationOperator.Equal,
                Seq(Difference(Call("incomparable", ceiling), i), Sp, Cup, Sp,
                    Difference(Call("lowerClosure", ceiling), Call("lowerClosure", boundary))))),
            "trace_eq_formula" => All("N", new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
                All("e", Call("Equiv", Call("Fin", F.Id("N")), p), All("I", set,
                    Imp(Call("ReverseExtension", F.Id("e")), Imp(Call("OrdConnected", i),
                        Rel(Call("trace", F.Id("e"), i, F.Id("N")), FormulaRelationOperator.Equal,
                            Call("formula", i))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        return Disp(All("P", new Formula.NamedConstant(FormulaIdentifier.Create("Type")),
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Sp, body)));
    }
}
