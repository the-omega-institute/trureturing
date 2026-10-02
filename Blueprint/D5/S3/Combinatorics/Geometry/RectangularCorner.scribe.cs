using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RectangularCornerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RectangularCorner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive global minima describe and count strict global floor corners.",
        H("Rectangular corners of order-convex sets"),
        Blocks(
            Paragraph(Text("For all natural m and n, Point(m,n) is Fin m times Fin n with coordinatewise order. Let I be an order-convex subset and let a belong to I. LocalMin(I,a,u) means that u is a global minimum of I and u is at most a. Adjacent(I,a,u,v) means that u and v satisfy LocalMin, the first coordinate of u is smaller, and no other such minimum has first coordinate strictly between them. Corner(I,a,b) means that b is globally maximal in the non-strict lower closure of I minus I, and both coordinates of b are strictly smaller than those of a. Global extremality is retained before imposing the coordinate restrictions. The dimensions may be zero; membership of a supplies nonemptiness whenever a is present.")),
            Definition("Point", "The finite rectangle", "Point(m,n) is Fin m times Fin n; the order compares both coordinates."),
            Definition("LocalMin", "Global minima below an included point", "Minimality is taken in all of I. The additional condition u at most a selects the minima below a."),
            Definition("Adjacent", "Consecutive minima by row", "The two selected global minima have increasing first coordinates and no selected global minimum strictly between those coordinates."),
            Definition("Corner", "Strict global floor corners", "Maximality is taken in the entire lower closure of I minus I. Both strict coordinate inequalities are imposed afterward."),
            Theorem("adjacent_gives_corner", "Consecutive minima give an exact corner", "Let u and v be consecutive selected global minima. If b has first coordinate value one less than v and second coordinate value one less than u, then b is a strict global floor corner below a. The antichain order forces the second coordinates to decrease. Absence of an intermediate minimum excludes included points below b; order-convexity proves global maximality of b in the floor."),
            Theorem("corner_gives_adjacent", "A corner recovers consecutive minima", "Every strict global floor corner b below a has global minima u and v below a that are consecutive by first coordinate, with b's first coordinate value plus one equal to v's and b's second coordinate value plus one equal to u's. The two immediate coordinate successors of b belong to I by global floor maximality; global minima below those successors recover u and v."),
            Theorem("rectangular_corner_card", "The exact corner count", "For every order-convex I and a in I, the number of strict global floor corners below a plus one equals the number of global minima of I at most a. The proof constructs a bijection from corners to the selected minima with their first minimum removed. Both geometric directions are used to prove the inverse and uniqueness. This general structural identity does not assert the full rowmotion homomesy conjecture, a toggle transport theorem, or an orbit identity."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rectangular-corner-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(F.Id(name), Open, Seq(arguments.SelectMany((value, index) =>
            index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
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
    private static Formula Not(Formula value) => Seq(Neg, Open, value, Close);
    private static Formula Inc(Formula value) => Seq(value, Sp, Plus, Sp, D(1));
    private static Formula Row(Formula value) =>
        Call("val", new Formula.Subscript(value, D(1)));
    private static Formula Column(Formula value) =>
        Call("val", new Formula.Subscript(value, D(2)));
    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);
    private static Formula Count(Formula point, Formula domain, Formula predicate) =>
        Call("card", Seq(OpenBrace, point, Sp, InMacro, Sp, domain,
            Sp, Mid, Sp, predicate, CloseBrace));

    private static Formula Statement(string name)
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var i = F.Id("I");
        var a = F.Id("a");
        var u = F.Id("u");
        var v = F.Id("v");
        var b = F.Id("b");
        var w = F.Id("w");
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var point = Call("Point", m, n);
        var localU = Call("LocalMin", i, a, u);
        var adjacent = Call("Adjacent", i, a, u, v);
        var corner = Call("Corner", i, a, b);
        var hr = Equal(Inc(Row(b)), Row(v));
        var hs = Equal(Inc(Column(b)), Column(u));
        Formula Points(Formula value, params string[] names)
        {
            foreach (var variable in names.Reverse()) value = All(variable, point, value);
            return value;
        }
        var rowOrder = Rel(Row(u), FormulaRelationOperator.LessThan, Row(v));
        var between = And(Rel(Row(u), FormulaRelationOperator.LessThan, Row(w)),
            Rel(Row(w), FormulaRelationOperator.LessThan, Row(v)));
        var noIntermediate = All("w", point, Imp(Call("LocalMin", i, a, w), Not(between)));
        var adjacentDefinition = And(localU,
            And(Call("LocalMin", i, a, v), And(rowOrder, noIntermediate)));
        var strictness = And(Rel(Row(b), FormulaRelationOperator.LessThan, Row(a)),
            Rel(Column(b), FormulaRelationOperator.LessThan, Column(a)));
        var floor = Seq(Call("lowerClosure", i), Sp, Setminus, Sp, i);
        var cornerDefinition = And(Call("Maximal", floor, b), strictness);
        Formula body = name switch
        {
            "Point" => Equal(point, Seq(Call("Fin", m), Sp, Times, Sp, Call("Fin", n))),
            "LocalMin" => Points(Iff(localU, And(Call("Minimal", i, u),
                Rel(u, FormulaRelationOperator.LessThanOrEqual, a))), "a", "u"),
            "Adjacent" => Points(Iff(adjacent, adjacentDefinition), "a", "u", "v"),
            "Corner" => Points(Iff(corner, cornerDefinition), "a", "b"),
            "adjacent_gives_corner" => Imp(Call("OrdConnected", i),
                Points(Imp(Member(a, i), Imp(adjacent, Imp(hr, Imp(hs, corner)))),
                    "a", "u", "v", "b")),
            "corner_gives_adjacent" => Imp(Call("OrdConnected", i),
                Points(Imp(Member(a, i), Imp(corner,
                    Some("u", point, Some("v", point, And(adjacent, And(hr, hs)))))),
                    "a", "b")),
            "rectangular_corner_card" => Imp(Call("OrdConnected", i),
                Points(Imp(Member(a, i), Equal(Inc(Count(b, point, corner)),
                    Count(u, point, localU))), "a")),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        if (name != "Point") body = All("I", Call("Set", point), body);
        return Disp(All("m", nat, All("n", nat, body)));
    }
}
