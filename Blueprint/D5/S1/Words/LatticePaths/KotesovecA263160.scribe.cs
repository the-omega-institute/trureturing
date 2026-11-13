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
            Paragraph(Text("Coordinates are labelled and steps are ordered. Each step decrements a nonempty subset by one. A path stops when any coordinate first reaches zero; simultaneous first zeros count once. Height zero or dimension zero admits only the empty path. The diagonal of this finite count is OEIS A263160. Write I(d,m,t) for the Lean internal_words count. The terminal-word identity and uniform estimates lead to its exact real-root limit along all natural indices. The proof uses only the cofinite range n at least two and imposes no fixed-dimension hypothesis.")),
            Node("Step", "Nonempty coordinate steps", StepFormula(), true, DescribeRole.Definition),
            Node("decrements", "Coordinate occurrences", DecrementsFormula(), false, DescribeRole.Definition),
            Node("FirstZero", "First-zero termination", FirstZeroFormula(), true, DescribeRole.Definition),
            Node("paths", "The literal finite path count", PathsFormula(), true, DescribeRole.Definition),
            Node("a", "The diagonal sequence", DiagonalFormula(), true, DescribeRole.Definition),
            Node("internal_words", "Internal words with bounded rows", InternalFormula(), false, DescribeRole.Definition),
            Node("first_zero_length_bound", "A finite path-length budget", LengthFormula(), false, DescribeRole.Theorem),
            Node("insertion_identity", "Transposing rows and inserting empty columns", InsertionFormula(), false, DescribeRole.Theorem),
            Node("internal_hasSum", "A positive geometric series", SeriesFormula(), false, DescribeRole.Theorem),
            Node("paths_eq_internal", "The literal terminal count", TerminalFormula(), false, DescribeRole.Theorem),
            Node("internal_count_upper", "A uniform factorial upper bound", UpperFormula(), false, DescribeRole.Theorem),
            Node("internal_count_lower", "A one-term lower bound", LowerFormula(), false, DescribeRole.Theorem),
            Node("internal_log_bounds", "Logarithmic factorial bounds", LogBoundsFormula(), false, DescribeRole.Theorem),
            Node("diagonal_log_estimate", "A quantitative diagonal error", ErrorFormula(), false, DescribeRole.Theorem),
            Node("diagonal_limit", "The complete diagonal real-root limit", LimitFormula(), false, DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool source, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("a263160-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            source ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(Commentary(name)))), role);

    private static string Commentary(string name) => name switch
    {
        "first_zero_length_bound" => "Every step uses at least one coordinate. Before the last step, each coordinate has been used at most h minus one times, so the length is at most d times (h minus one), plus one. This is the cutoff in the terminal-word sum. Height zero or dimension zero still admits only the empty path; for positive height and dimension the cutoff is at most d times h, making the finite count exhaustive.",
        "insertion_identity" => "A row chooses at most m positions among k labelled columns. Transposition identifies these independent rows with columns that may be empty. Removing the empty columns gives an internal word; choosing its positions gives the binomial coefficient.",
        "internal_hasSum" => "The length budget truncates the insertion polynomial at d times m. Each geometric binomial column has sum two. Exchanging the finite sum with the convergent series gives twice the internal-word count.",
        "paths_eq_internal" => "Appending a nonempty coordinate subset to an internal word either remains internal or reaches its first zero. These cases partition words, including simultaneous first zeros. Summing over lengths cancels the nonempty internal words and retains the unique empty word.",
        "internal_count_upper" => "Vandermonde and the factorial binomial bound dominate each row polynomial by the shifted degree-m monomial divided by m factorial. A shift by m reduces the geometric moment to Mathlib's sum-integral and Gamma estimate. The polynomial and exponential are compared as separate monotone factors.",
        "internal_count_lower" => "Every term of the positive series is at most its sum. The lower factorial bound for the binomial coefficient supplies the displayed term. Subtraction inside the natural-number cast is truncated natural subtraction.",
        "internal_log_bounds" => "For the lower estimate take k equal to the ceiling of m times d divided by log two, plus m. The ceiling error costs at most one exponential step. Taking logarithms of that term and of the uniform upper bound gives the sandwich.",
        "diagonal_log_estimate" => "Set d to n and m to n minus one. Mathlib's factorial-log bounds cancel the main factorial terms. The terminal-count comparison contributes only a linear error; the displayed bound is at most a constant times n log n.",
        "diagonal_limit" => "Divide the quantitative logarithmic error by n squared and use log n divided by n tending to zero. Positivity of the finite count allows conversion of the real power to an exponential. Continuity of the exponential yields one divided by log two along every natural index.",
        _ => "The displayed formula specifies the objects and their ordered finite counts.",
    };

    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula Cast(Formula x) => Qualified("Nat", "cast", x);
    private static Formula Log(Formula x) => Qualified("Real", "log", x);
    private static Formula Fact(Formula x) => Qualified("Nat", "factorial", x);
    private static Formula C() => Log(D(2));
    private static Formula HCount(Formula d, Formula m) => Mul(D(2), Sum("t", Range(Add(Mul(d, m), D(1))), Cast(Call("I", d, m, F.Id("t")))));
    private static Formula Row(Formula k, Formula m) => Cast(Sum("r", Range(Add(m, D(1))), Choose(k, F.Id("r"))));
    private static Formula AllDM(Formula body) => All("d", N(), All("m", N(), body));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
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
            Eq(Call("I", d, m, t), Card(words))))));
    }

    private static Formula LengthFormula()
    {
        var d = F.Id("d"); var h = F.Id("h"); var w = F.Id("w");
        return Disp(All("d", N(), All("h", N(), All("w", List(Step(d)),
            Imp(Call("FirstZero", h, w), Le(Length(w), Add(Mul(d, Sub(h, D(1))), D(1))))))));
    }

    private static Formula InsertionFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var k = F.Id("k"); var r = F.Id("r"); var t = F.Id("t");
        var lhs = new Formula.Power(Par(Sum("r", Range(Add(m, D(1))), Choose(k, r))), d);
        var rhs = Sum("t", Range(Add(k, D(1))), Mul(Choose(k, t), Call("I", d, m, t)));
        return Disp(All("d", N(), All("m", N(), All("k", N(), Eq(lhs, rhs)))));
    }
    private static Formula SeriesFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var k = F.Id("k");
        return Disp(AllDM(Call("HasSum", Lam("k", N(),
            Mul(Pow(Div(D(1), D(2)), k), Pow(Row(k, m), d))), HCount(d, m))));
    }

    private static Formula TerminalFormula()
    {
        var d = F.Id("d"); var m = F.Id("m");
        return Disp(AllDM(Imp(Lt(D(0), d), Eq(Call("paths", d, Add(m, D(1))),
            Add(D(1), Mul(Sub(Pow(D(2), d), D(2)),
                Sum("t", Range(Add(Mul(d, m), D(1))), Call("I", d, m, F.Id("t")))))))));
    }

    private static Formula UpperFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var n = Mul(m, d);
        var numerator = Mul(Pow(D(2), Add(m, D(1))), Cast(Fact(n)));
        var denominator = Mul(Pow(C(), Add(n, D(1))), Pow(Cast(Fact(m)), d));
        return Disp(AllDM(Le(HCount(d, m), Div(numerator, denominator))));
    }

    private static Formula LowerFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var k = F.Id("k");
        return Disp(AllDM(All("k", N(), Le(Div(Mul(Pow(Div(D(1), D(2)), k),
            Pow(Cast(Sub(Add(k, D(1)), m)), Mul(m, d))), Pow(Cast(Fact(m)), d)), HCount(d, m)))));
    }

    private static Formula LogBoundsFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var n = Cast(Mul(m, d));
        var loss = Mul(Cast(d), Log(Cast(Fact(m))));
        var lower = Sub(Sub(Sub(Mul(n, Log(Div(n, C()))), n), Mul(Add(Cast(m), D(1)), C())), loss);
        var upper = Sub(Sub(Add(Mul(Add(Cast(m), D(1)), C()), Log(Cast(Fact(Mul(m, d))))),
            Mul(Add(n, D(1)), Log(C()))), loss);
        return Disp(AllDM(Imp(Lt(D(0), d), Imp(Lt(D(0), m),
            And(Le(lower, Log(HCount(d, m))), Le(Log(HCount(d, m)), upper))))));
    }

    private static Formula ErrorFormula()
    {
        var n = F.Id("n"); var r = Cast(n);
        var error = new Formula.Absolute(Sub(Log(Cast(Call("a", n))),
            Mul(Pow(r, D(2)), Sub(Log(r), Log(C())))));
        var bound = Mul(r, Add(Add(Mul(D(4), Log(r)), D(6)), Mul(D(2), new Formula.Absolute(Log(C())))));
        return Disp(All("n", N(), Imp(Le(D(2), n), Le(error, bound))));
    }

    private static Formula LimitFormula()
    {
        var n = F.Id("n"); var r = Cast(n);
        var sequence = Lam("n", N(), Div(Qualified("Real", "rpow", Cast(Call("a", n)),
            Div(D(1), Pow(r, D(2)))), r));
        return Disp(Call("Tendsto", sequence, F.Id("atTop"), Call("nhds", Div(D(1), C()))));
    }

}
