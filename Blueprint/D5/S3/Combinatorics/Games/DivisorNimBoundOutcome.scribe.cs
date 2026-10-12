using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundOutcomeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A position has zero Sprague–Grundy value precisely when an even number of "
            + "heaps attain its least dyadic valuation.",
        H("Dyadic Depth and Zero Positions"),
        Blocks(
            Node("valuation", "Dyadic valuation", "valuation", ValuationFormula(),
                "The dyadic valuation of a positive integer is the exponent of two in "
                    + "its prime factorization.", DescribeRole.Definition),
            Node("has-depth", "Position depth", "HasDepth", DepthFormula(),
                "Every heap has valuation at least k, and at least one heap has "
                    + "valuation exactly k.", DescribeRole.Definition),
            Node("count-at", "Heaps at a depth", "countAt", CountFormula(),
                "Count heap occurrences of valuation k, retaining their multiplicities.",
                DescribeRole.Definition),
            Node("subtract-lower", "Subtracting at a lower valuation", "valuation_sub_of_lt",
                SubtractLowerFormula(),
                "When the removed amount has smaller valuation than the heap, the "
                    + "positive remainder has the valuation of that amount.", DescribeRole.Theorem),
            Node("lower-move", "Lower-depth moves create one minimum heap", "lower_move",
                LowerMoveFormula(),
                "A removal of valuation j below the position depth creates exactly "
                    + "one heap at depth j. Every unchanged heap remains at greater depth.",
                DescribeRole.Theorem),
            Node("subtract-same", "Equal-valuation subtraction", "valuation_sub_same",
                SubtractSameFormula(),
                "Subtracting two positive integers of the same dyadic valuation "
                    + "either gives zero or raises the valuation.", DescribeRole.Theorem),
            Node("high-move", "Moves retaining a minimum heap change parity", "high_move_count",
                HighMoveFormula(),
                "If an unchanged heap retains the minimum depth, any removal at least "
                    + "that deep has valuation exactly equal to the depth. It either "
                    + "adds or removes one minimum-depth heap, so the count changes parity.",
                DescribeRole.Theorem),
            Node("even-to-odd", "Every move from an even count has an odd count",
                "even_count_moves_odd", EvenMovesFormula(),
                "An even positive minimum-depth count is at least two. A lower removal "
                    + "creates a single minimum; every other legal removal leaves a "
                    + "minimum heap and changes the parity of its count.", DescribeRole.Theorem),
            Node("odd-to-even", "An odd count has a zero-count follower",
                "odd_count_has_even_move", OddMoveFormula(),
                "With at least three minimum-depth heaps, subtract the depth power "
                    + "from one of them. With a unique minimum and another heap, subtract "
                    + "that power from the other heap. A singleton is removed entirely.",
                DescribeRole.Theorem),
            Node("zero-characterization", "Zero value is equivalent to an even count",
                "zero_iff_even_count", ZeroFormula(),
                "Induction on the total number of stones applies the mex rule to the "
                    + "two parity properties: an even count has no zero-valued follower, "
                    + "while an odd count has a zero-valued follower.", DescribeRole.Theorem),
            Node("high-nonzero", "Nonzero high-removal followers require a unique minimum",
                "high_nonzero_unique", UniqueFormula(),
                "For a nonzero parent, a high removal retaining a minimum-depth heap "
                    + "would change an odd count to an even count and produce value zero. "
                    + "Thus a nonzero follower can arise only by changing the unique minimum.",
                DescribeRole.Theorem),
            Node("valuation-decomposition", "Power of two times an odd factor",
                "valuation_decomposition", DecompositionFormula(),
                "Every positive heap size is a power of two times a positive odd integer.",
                DescribeRole.Theorem),
            Node("multiple-odd", "At least two odd heaps give value at most one",
                "depth_zero_multiple", MultipleFormula(),
                "There are no lower-valuation removals at depth zero. With more than "
                    + "one odd heap, every follower of a nonzero parent has value zero.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Position() => Call("Multiset", Nat());
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Not(Eq(a, b));
    private static Formula Mem(Formula a, Formula b) => Call("mem", a, b);
    private static Formula Power(Formula k) => Seq(D(2), Caret, Grp(k));
    private static Formula Val(Formula h) => Call("valuation", h);
    private static Formula Depth(Formula p, Formula k) => Call("HasDepth", p, k);
    private static Formula Count(Formula p, Formula k) => Call("countAt", p, k);
    private static Formula Grundy(Formula p) => Call("grundy", p);
    private static Formula Next(Formula p, Formula h, Formula d) => Call("successor", p, h, d);
    private static Formula Nats(Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; --i) body = All(names[i], Nat(), body);
        return body;
    }
    private static Formula MovesPremise(Formula p, Formula h, Formula d, Formula k) =>
        And(Call("Positive", p), And(Depth(p, k), And(Mem(h, p), Call("legal", p, h, d))));

    private static Formula ValuationFormula()
    {
        var h = F.Id("h");
        return Disp(All("h", Nat(), Eq(Val(h), Call("padicValNat", D(2), h))));
    }
    private static Formula DepthFormula()
    {
        var p = F.Id("P"); var k = F.Id("k"); var h = F.Id("h");
        return Disp(All("P", Position(), All("k", Nat(), Iff(Depth(p, k),
            And(All("h", Nat(), Imp(Mem(h, p), Le(k, Val(h)))),
                Exists("h", Nat(), And(Mem(h, p), Eq(Val(h), k))))))));
    }
    private static Formula CountFormula()
    {
        var p = F.Id("P"); var k = F.Id("k"); var h = F.Id("h");
        var heaps = Seq(OpenBrace, h, Sp, InMacro, Sp, p, Sp, Bar, Sp,
            Eq(Val(h), k), CloseBrace);
        return Disp(All("P", Position(), All("k", Nat(), Eq(Count(p, k), Call("card", heaps)))));
    }
    private static Formula SubtractLowerFormula()
    {
        var h = F.Id("h"); var d = F.Id("d");
        return Disp(Nats(Imp(And(Lt(D(0), d), And(Le(d, h), Lt(Val(d), Val(h)))),
            And(Lt(D(0), Sub(h, d)), Eq(Val(Sub(h, d)), Val(d)))), "h", "d"));
    }
    private static Formula LowerMoveFormula()
    {
        var p = F.Id("P"); var h = F.Id("h"); var d = F.Id("d");
        var j = F.Id("j"); var k = F.Id("k"); var q = Next(p, h, d);
        return Disp(All("P", Position(), Nats(Imp(And(MovesPremise(p, h, d, k),
            And(Eq(Val(d), j), Lt(j, k))), And(Depth(q, j), Eq(Count(q, j), D(1)))),
            "h", "d", "j", "k")));
    }
    private static Formula SubtractSameFormula()
    {
        var h = F.Id("h"); var d = F.Id("d"); var k = F.Id("k");
        return Disp(Nats(Imp(And(Lt(D(0), h), And(Lt(D(0), d), And(Le(d, h),
            And(Eq(Val(h), k), And(Eq(Val(d), k), Ne(Sub(h, d), D(0))))))),
            Lt(k, Val(Sub(h, d)))), "h", "d", "k"));
    }
    private static Formula HighMoveFormula()
    {
        var p = F.Id("P"); var h = F.Id("h"); var d = F.Id("d"); var k = F.Id("k");
        var q = Next(p, h, d);
        return Disp(All("P", Position(), Nats(Imp(And(MovesPremise(p, h, d, k),
            And(Le(k, Val(d)), Lt(D(0), Count(Call("erase", p, h), k)))),
            And(Depth(q, k), Eq(Call("mod", Add(Count(q, k), Count(p, k)), D(2)), D(1)))),
            "h", "d", "k")));
    }
    private static Formula EvenMovesFormula()
    {
        var p = F.Id("P"); var q = F.Id("Q"); var j = F.Id("j"); var k = F.Id("k");
        return Disp(All("P", Position(), All("Q", Position(), All("k", Nat(),
            Imp(And(Call("Positive", p), And(Depth(p, k), And(Call("Even", Count(p, k)),
                Mem(q, Call("moves", p))))), Exists("j", Nat(), And(Depth(q, j),
                    Eq(Call("mod", Count(q, j), D(2)), D(1)))))))));
    }
    private static Formula OddMoveFormula()
    {
        var p = F.Id("P"); var q = F.Id("Q"); var j = F.Id("j"); var k = F.Id("k");
        return Disp(All("P", Position(), All("k", Nat(), Imp(And(Call("Positive", p),
            And(Depth(p, k), Eq(Call("mod", Count(p, k), D(2)), D(1)))),
            Exists("Q", Position(), And(Mem(q, Call("moves", p)), Or(Eq(q, D(0)),
                Exists("j", Nat(), And(Depth(q, j), Call("Even", Count(q, j)))))))))));
    }
    private static Formula ZeroFormula()
    {
        var p = F.Id("P"); var k = F.Id("k");
        return Disp(All("P", Position(), All("k", Nat(), Imp(And(Call("Positive", p),
            Depth(p, k)), Iff(Eq(Grundy(p), D(0)), Call("Even", Count(p, k)))))));
    }
    private static Formula UniqueFormula()
    {
        var p = F.Id("P"); var h = F.Id("h"); var d = F.Id("d"); var k = F.Id("k");
        return Disp(All("P", Position(), Nats(Imp(And(MovesPremise(p, h, d, k),
            And(Le(k, Val(d)), And(Ne(Grundy(p), D(0)), Ne(Grundy(Next(p, h, d)), D(0))))),
            And(Eq(Count(p, k), D(1)), Eq(Val(h), k))), "h", "d", "k")));
    }
    private static Formula DecompositionFormula()
    {
        var m = F.Id("m"); var u = F.Id("u");
        return Disp(All("m", Nat(), Imp(Lt(D(0), m), Exists("u", Nat(),
            And(Lt(D(0), u), And(Call("Odd", u), Eq(m, Mul(Power(Val(m)), u))))))));
    }
    private static Formula MultipleFormula()
    {
        var p = F.Id("P");
        return Disp(All("P", Position(), Imp(And(Call("Positive", p),
            And(Depth(p, D(0)), Lt(D(1), Count(p, D(0))))), Le(Grundy(p), D(1)))));
    }
}
