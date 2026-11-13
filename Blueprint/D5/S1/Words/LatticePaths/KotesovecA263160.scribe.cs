using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.LatticePaths;

internal sealed class KotesovecA263160Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/LatticePaths/KotesovecA263160.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/kotesovec2026a263160");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal first-zero lattice paths and row/column insertion.",
        H("First-zero paths"),
        Blocks(
            Paragraph(Text("Coordinates are labelled and steps are ordered. Each step decrements a nonempty subset by one. A path stops when any coordinate first reaches zero; simultaneous first zeros count once. Height zero or dimension zero admits only the empty path. The diagonal of this finite count is OEIS A263160. Its conjectured real-root limit is not asserted by the finite counting identities below.")),
            Node("Step", "Nonempty coordinate steps", StepFormula(), true, DescribeRole.Definition),
            Node("decrements", "Coordinate occurrences", DecrementsFormula(), false, DescribeRole.Definition),
            Node("FirstZero", "First-zero termination", FirstZeroFormula(), true, DescribeRole.Definition),
            Node("paths", "The literal finite path count", PathsFormula(), true, DescribeRole.Definition),
            Node("a", "The diagonal sequence", DiagonalFormula(), true, DescribeRole.Definition),
            Node("internal_words", "Internal words with bounded rows", InternalFormula(), false, DescribeRole.Definition),
            Node("first_zero_length_bound", "A finite path-length budget", LengthFormula(), false, DescribeRole.Theorem),
            Node("insertion_identity", "Transposing rows and inserting empty columns", InsertionFormula(), false, DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool source, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("a263160-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            source ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(name == "first_zero_length_bound"
                ? "Every step uses at least one coordinate. Before the last step, each coordinate has been used at most one less than the initial height. This bounds the length and makes the displayed finite count exhaustive."
                : name == "insertion_identity"
                    ? "A row chooses at most m positions among k labelled columns. Transposition identifies these independent rows with columns that may be empty. Removing the empty columns gives an internal word; choosing its positions gives the binomial coefficient."
                    : "The displayed formula specifies the objects and their ordered finite counts."))), role);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Nat(Formula x) => Par(Seq(x, Colon, Sp, N()));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Or, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Lam(string x, Formula type, Formula body) =>
        Par(Seq(F.Id(x), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Step(Formula d) => Call("Step", d);
    private static Formula List(Formula t) => Call("List", t);
    private static Formula Dec(Formula w, Formula i) => Call("decrements", w, i);
    private static Formula Length(Formula w) => Qualified("List", "length", w);
    private static Formula OfFn(Formula w) => Qualified("List", "ofFn", w);
    private static Formula Val(Formula s) => Qualified("Subtype", "val", s);
    private static Formula Card(Formula t) => Qualified("Fintype", "card", t);
    private static Formula Sum(string x, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(x), Sp, InMacro, Sp, set)), Sp, body);
    private static Formula Range(Formula n) => Qualified("Finset", "range", n);
    private static Formula Choose(Formula n, Formula k) => Qualified("Nat", "choose", n, k);

    private static Formula StepFormula()
    {
        var d = F.Id("d"); var s = F.Id("s");
        return Disp(All("d", N(), Eq(Step(d), Call("Subtype", Lam("s", Call("Finset", Fin(d)),
            Qualified("Finset", "Nonempty", s))))));
    }

    private static Formula DecrementsFormula()
    {
        var d = F.Id("d"); var w = F.Id("w"); var i = F.Id("i"); var s = F.Id("s");
        var predicate = Lam("s", Step(d), Call("decide", Mem(i, Val(s))));
        return Disp(All("d", N(), All("w", List(Step(d)), All("i", Fin(d),
            Eq(Dec(w, i), Qualified("List", "countP", predicate, w))))));
    }

    private static Formula FirstZeroFormula()
    {
        var d = F.Id("d"); var h = F.Id("h"); var w = F.Id("w"); var r = F.Id("r"); var i = F.Id("i");
        var interior = All("r", N(), Imp(Lt(r, Length(w)), All("i", Fin(d),
            Lt(Dec(Qualified("List", "take", r, w), i), h))));
        var terminal = Ex("i", Fin(d), Eq(Dec(w, i), h));
        var value = Call("ite", Or(Eq(h, D(0)), Eq(d, D(0))),
            Eq(w, Qualified("List", "nil")), And(interior, terminal));
        return Disp(All("d", N(), All("h", N(), All("w", List(Step(d)),
            Eq(Call("FirstZero", h, w), value)))));
    }

    private static Formula PathsFormula()
    {
        var d = F.Id("d"); var h = F.Id("h"); var t = F.Id("t"); var w = F.Id("w");
        var words = Call("Subtype", Lam("w", new Formula.TypeArrow(Fin(t), Step(d)), Call("FirstZero", h, OfFn(w))));
        return Disp(All("d", N(), All("h", N(), Eq(Call("paths", d, h),
            Sum("t", Range(Add(Mul(d, h), D(1))), Card(words))))));
    }

    private static Formula DiagonalFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", N(), Eq(Call("a", n), Call("paths", n, n))));
    }

    private static Formula InternalFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var t = F.Id("t"); var w = F.Id("w"); var i = F.Id("i");
        var words = Call("Subtype", Lam("w", new Formula.TypeArrow(Fin(t), Step(d)),
            All("i", Fin(d), Le(Dec(OfFn(w), i), m))));
        return Disp(All("d", N(), All("m", N(), All("t", N(),
            Eq(Call("internal_words", d, m, t), Card(words))))));
    }

    private static Formula LengthFormula()
    {
        var d = F.Id("d"); var h = F.Id("h"); var w = F.Id("w");
        return Disp(All("d", N(), All("h", N(), All("w", List(Step(d)),
            Imp(Call("FirstZero", h, w), Le(Length(w), Mul(d, h)))))));
    }

    private static Formula InsertionFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var k = F.Id("k"); var r = F.Id("r"); var t = F.Id("t");
        var lhs = new Formula.Power(Par(Sum("r", Range(Add(m, D(1))), Choose(k, r))), d);
        var rhs = Sum("t", Range(Add(k, D(1))), Mul(Choose(k, t), Call("internal_words", d, m, t)));
        return Disp(All("d", N(), All("m", N(), All("k", N(), Eq(lhs, rhs)))));
    }
}
