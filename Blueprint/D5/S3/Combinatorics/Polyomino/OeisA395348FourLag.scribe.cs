using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class OeisA395348FourLagDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/karlssonsloane2026a395348");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal alternating spiral-queens play exists uniquely and satisfies the four-lag recurrence.",
        H("The four-lag recurrence for OEIS A395348"),
        Blocks(
            Paragraph(Text("The Black label at sequence index n is the chronological label at turn 2n. Red moves at odd turns.")),
            Node("Attacks", "Queen lines", Attacks(), "A queen attacks along either coordinate axis and along each of the two diagonal projections.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SpiralLegal", "Legal labels", SpiralLegal(), "Every earlier turn forbids overlap. The row, column and diagonal tests apply to earlier turns of the other parity.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SpiralGreedy", "Least legal label", SpiralGreedy(), "At every turn the chosen label is legal and all smaller natural labels are illegal.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a395348_four_lag", "Existence, uniqueness and the four-lag recurrence", FourLag(), "The opening proof checks all fourteen turns inside a radius-four box. From shell five onward, the earlier opposing rows, columns and two diagonal projections exclude smaller labels on each of the four turns. Two shells preserve parity. The two Black slots give increments 16r+10 and 16r+18, with the n=2 case coming from the opening. The lower bound is necessary because in the unique least-label play a(0)=0 and a(4)=38, whereas the claimed increment would give 34. Also a(1)=2 and a(5)=52, whereas the claimed increment would give 44.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("oeisa395348fourlag-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Int => Seq(Mathbb, Grp(V("Z")));
    private static Formula Board => P(Seq(Int, Sp, Times, Sp, Int));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Binder(string name, Formula type) => P(Seq(V(name), Sp, Colon, Sp, type));
    private static Formula Bind(Formula token, string name, Formula type, Formula body) =>
        Seq(token, Sp, Binder(name, type), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Or, P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Iff, P(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula f) => P(Seq(f, Sp, Colon, Sp, Int));
    private static Formula NegateProp(Formula f) => Seq(Neg, Sp, P(f));
    private static Formula Coord(Formula f, byte n) => Seq(f, Dot, D(n));

    private static Formula Moves => new Formula.TypeArrow(Nat, Nat);
    private static Formula IsLegal(Formula f, Formula t, Formula n) => Call("SpiralLegal", f, t, n);
    private static Formula Plays(Formula f) => Call("SpiralGreedy", f);

    private static Formula Attacks()
    {
        var q = V("q");
        var p = V("p");
        var x = Coord(q, 1);
        var y = Coord(q, 2);
        var u = Coord(p, 1);
        var v = Coord(p, 2);
        return All("q", Board, All("p", Board, IffTo(Call("Attacks", q, p),
            Or(Eq(x, u), Or(Eq(y, v), Or(Eq(Add(x, y), Add(u, v)), Eq(Sub(x, y), Sub(u, v))))))));
    }

    private static Formula SpiralLegal()
    {
        var f = V("f");
        var t = V("t");
        var n = V("n");
        var j = V("j");
        var otherColor = Ne(new Formula.Modulo(Cast(j), D(2)), new Formula.Modulo(Cast(t), D(2)));
        var attack = Call("Attacks", Call("spiral", App(f, j)), Call("spiral", n));
        var rule = All("j", Nat, Imp(Lt(j, t), And(Ne(App(f, j), n), Imp(otherColor, NegateProp(attack)))));
        return All("f", Moves, All("t", Nat, All("n", Nat, IffTo(IsLegal(f, t, n), rule))));
    }

    private static Formula SpiralGreedy()
    {
        var f = V("f");
        var t = V("t");
        var n = V("n");
        var least = All("n", Nat, Imp(Lt(n, App(f, t)), NegateProp(IsLegal(f, t, n))));
        return All("f", Moves, IffTo(Plays(f), All("t", Nat, And(IsLegal(f, t, App(f, t)), least))));
    }

    private static Formula FourLag()
    {
        var f = V("f");
        var n = V("n");
        var unique = Call("ExistsUnique", P(Seq(Binder("f", Moves), Sp, Mapsto, Sp, Plays(f))));
        var law = Eq(App(f, Mul(D(2), P(Add(n, D(4))))),
            Add(Add(App(f, Mul(D(2), n)), Mul(D(8), n)), D(3, 4)));
        return And(unique, All("f", Moves, Imp(Plays(f), All("n", Nat, Imp(Le(D(2), n), law)))));
    }
}
