using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class SquareSpiralShellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/SquareSpiralShells.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/karlssonsloane2026a395348");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive index of the reflected square spiral belongs to its computed shell and side.",
        H("The square spiral by shells"),
        Blocks(
            Paragraph(Text("Reflect the horizontal coordinate of the Irwin walk to start east, north, west and south in the source coordinates. The origin has label zero. Each positive shell comprises four half-open sides, with each corner assigned to one side.")),
            Node("shellPoint", "A position on a shell", ShellPoint(), "The four clauses run up the right edge, left along the top, down the left edge and right along the bottom.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("spiral", "The source spiral walk", Spiral(), "Use the cell of the original Irwin walk at the given index and reverse its horizontal coordinate.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spiral_shells", "Shell and side of a positive index", SpiralShells(), "The first label of shell k+1 is the odd square (2k+1) squared. The next start is greater by 8(k+1). Irwin’s two-leg layer lemma gives the cells on the four sides after reflection. Positivity of the index is necessary because the origin has index zero, while every displayed shell starts at an odd square at least one and has a nonnegative side offset.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("squarespiralshells-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Int => Seq(Mathbb, Grp(V("Z")));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Pair(Formula a, Formula b) => P(Seq(a, Comma, Sp, b));
    private static Formula Binder(string name, Formula type) => P(Seq(V(name), Sp, Colon, Sp, type));
    private static Formula Bind(Formula token, string name, Formula type, Formula body) =>
        Seq(token, Sp, Binder(name, type), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Ex(string name, Formula type, Formula body) => Bind(Exists, name, type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula f) => P(Seq(f, Sp, Colon, Sp, Int));
    private static Formula Negate(Formula f) => Seq(Minus, f);
    private static Formula Coord(Formula f, byte n) => Seq(f, Dot, D(n));

    private static Formula If(Formula test, Formula yes, Formula no) =>
        P(Seq(V("if"), Sp, test, Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no));

    private static Formula ShellPoint()
    {
        var r = V("r");
        var d = V("d");
        var right = Pair(r, Add(Sub(d, r), D(1)));
        var top = Pair(Sub(Sub(Mul(D(3), r), D(1)), d), r);
        var left = Pair(Negate(r), Sub(Sub(Mul(D(5), r), D(1)), d));
        var bottom = Pair(Add(Sub(d, Mul(D(7), r)), D(1)), Negate(r));
        var value = If(Lt(d, Mul(D(2), r)), right,
            If(Lt(d, Mul(D(4), r)), top, If(Lt(d, Mul(D(6), r)), left, bottom)));
        return All("r", Int, All("d", Int, Eq(Call("shellPoint", r, d), value)));
    }

    private static Formula Spiral()
    {
        var n = V("n");
        var cell = Seq(P(Call("walk", n)), Dot, V("cell"));
        return All("n", Nat, Eq(Call("spiral", n), Pair(Negate(Coord(cell, 1)), Coord(cell, 2))));
    }

    private static Formula SpiralShells()
    {
        var n = V("n");
        var k = V("k");
        var d = V("d");
        var odd = P(Add(Mul(D(2), k), D(1)));
        var range = Lt(d, Mul(D(8), P(Add(k, D(1)))));
        var point = Eq(Call("spiral", n), Call("shellPoint", Add(Cast(k), D(1)), Cast(d)));
        return All("n", Nat, Imp(Lt(D(0), n), Ex("k", Nat, Ex("d", Nat,
            And(Eq(n, Add(Mul(odd, odd), d)), And(range, point))))));
    }
}
