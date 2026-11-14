using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionCommutationCriterionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/striker2018generalizedtoggles");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete commutation relation of guarded interval-closed toggles on arbitrary partial orders.",
        H("A complete criterion for commuting interval-closed toggles"), Blocks(
            Paragraph(Text("Let P be any partially ordered set. A subset S is order-convex when it contains every point between each pair of its members. The operation toggle(x,S) changes membership at x precisely when the resulting set is order-convex, and otherwise retains S. The criterion concerns equality of both compositions on every order-convex starting set. It uses this original guarded operation at both stages.")),
            Describe.Lean(
                DescribeId.Create("rowmotion-toggles-commute-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/RowmotionCommutationCriterion.toggles_commute_iff"),
                H("Complete commutation criterion"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For distinct points in a finite partially ordered set, Striker's Lemma 3.17 gives the criterion: the points are incomparable, or one covers the other and the lower point is minimal while the upper point is maximal. The Lean theorem includes equal points explicitly and proves the same characterization for arbitrary partial orders, without finiteness or local finiteness.")),
                    Paragraph(Text("For sufficiency at an extremal covering pair x below y, compare two order-convex sets that agree away from y. Legality of flipping x transfers between them. When an interval after the flip has x as its lower endpoint and y as its upper endpoint, the covering condition leaves only those endpoints. In the remaining intervals involving x, maximality of y permits transfer of all required memberships. If the interval does not involve x, its membership follows from convexity of the starting set and minimality of x. Applying this transfer to S and toggle(y,S) shows that toggling y preserves the guard for x; order duality supplies the other guard. The two guarded compositions then agree in all four combinations of guard values. This argument does not assert that either flip is always legal. The incomparable case directly reuses incomparable_toggles_commute.")),
                    Paragraph(Text("For necessity, suppose x is strictly below y. If a point lies strictly between them, toggling the empty set in the two orders leaves different singletons, because the two-point set is not order-convex. Thus x must be covered by y. If z is strictly below x, start with S consisting of all points strictly below y. Removing x gives an order-convex set T: a point above x and strictly below y would contradict the cover. Adding y instead gives the closed lower interval through y. The two further flips are both blocked by the missing point x between z and y. The compositions therefore give T and that closed lower interval, distinguished by membership at y. This proves minimality of x without choosing a covered predecessor. Order duality proves maximality of y.")),
                    Paragraph(Text("The criterion gives the commutation relation needed when organizing compositions of the existing interval-closed toggles. It does not prove a rowmotion orbit formula, a return-period count, or a homomesy statement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Par(left), op, Par(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Or, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Statement()
    {
        var p = F.Id("P");
        var x = F.Id("x");
        var y = F.Id("y");
        var s = F.Id("S");
        var equality = new Formula.Relation(
            Call("toggle", x, Call("toggle", y, s)), FormulaRelationOperator.Equal,
            Call("toggle", y, Call("toggle", x, s)));
        var commutes = All("S", Call("Set", p),
            Logic(Call("OrdConnected", s), FormulaLogicOperator.Implies, equality));
        var cases = Or(new Formula.Relation(x, FormulaRelationOperator.Equal, y),
            Or(And(new Formula.Not(Par(LE(x, y))), new Formula.Not(Par(LE(y, x)))),
                Or(And(Call("IsMin", x), And(Call("IsMax", y), Call("CovBy", x, y))),
                    And(Call("IsMin", y), And(Call("IsMax", x), Call("CovBy", y, x))))));
        return All("P", F.Id("Type"),
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Comma, Sp,
                All("x", p, All("y", p, Logic(commutes, FormulaLogicOperator.Iff, cases)))));
    }
}
