using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class FibonacciMapFirstStartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/FibonacciMapFirstStart.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/joshirust2025monochromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locate the first longest monochromatic progression at every Fibonacci difference.",
        H("First Starts at Fibonacci Differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-map-first-start-definition"),
                DeclarationHandle.Create(Prefix + "goldenMAPFirstStart"),
                H("The first start of a longest progression"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "goldenWord is the zero-indexed fixed point 010010100100101... "
                    + "of 0 -> 01 and 1 -> 0. True represents 0 and false represents 1. "
                    + "goldenMAPMaximum(d) is the supremum of all positive progression "
                    + "lengths over every natural start and both letters. The definition "
                    + "takes the natural infimum of starts attaining that length, without "
                    + "choosing a letter in advance. At the Fibonacci differences below "
                    + "the length set is bounded and its maximum is attained, so the "
                    + "start set is nonempty and its infimum is its least element."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-map-open-rotation-run"),
                DeclarationHandle.Create(Prefix + "open_rotation_run"),
                H("An orbit confined to an open interval"),
                StatementSource.FromAuthor(OpenRotationRunFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let x be a finite orbit of rotation by a positive step eps, "
                    + "forward or backward according to the Boolean forward. If all "
                    + "length points lie in (lo,hi) inside [0,1], and eps is at most "
                    + "the complementary gap, no step wraps around. The last point "
                    + "is therefore the first point plus the signed total displacement, "
                    + "whose magnitude is strictly less than hi-lo. The subtraction "
                    + "length-1 is natural subtraction before coercion to the reals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-map-first-start-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both parity families"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Here fib is the natural Fibonacci sequence, with fib(0)=0 "
                        + "and fib(1)=1. For every n at least one both differences are "
                        + "positive. The two equations describe the earliest starts "
                        + "attaining the global maximum, not just starts of particular "
                        + "progression witnesses.")),
                    Paragraph(Text(
                        "Write r=1/tau and m for the Fibonacci index. At word position j "
                        + "the phase is {(j+1)tau}, and true letters occupy (r^2,1). "
                        + "The step is r^m to the right for odd m and r^m to the left "
                        + "for even m. The natural maximum length is fib(m-2)+fib(m) "
                        + "for odd m and one more for even m. Open symbol endpoints "
                        + "prevent wraparound even when m=2 and the step equals r^2. "
                        + "Every false-letter progression is strictly shorter.")),
                    Paragraph(Text(
                        "Cassini's integer determinant gives one-sided orbit records: "
                        + "before fib(m+2), the positive displacement for odd m, or the "
                        + "backward displacement for even m, is at least r^m. "
                        + "In integral Fibonacci coordinates a smaller displacement "
                        + "would force a denominator at least fib(m)+fib(m+1). "
                        + "The odd maximal-start interval translates by one extra "
                        + "rotation to a positive interval shorter than r^m. "
                        + "The even interval has backward width r^(2m-1), smaller "
                        + "than the preceding even record r^(2m-2). These exclusions "
                        + "rule out every earlier start. The boundary n=1 gives "
                        + "first starts 3 at difference 2 and 2 at difference 1."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("joshi-rust-fibonacci-map-first-start"),
                    ResolutionKind.Proved)))));

    private static Formula DefinitionFormula()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var c = F.Id("c");
        var k = F.Id("k");
        var run = Bind(FormulaQuantifier.Exists, "c", F.Id("Bool"),
            Bind(FormulaQuantifier.ForAll, "k", Naturals(),
                Implies(Less(k, Call("goldenMAPMaximum", d)),
                    Equal(Call("goldenWord", Add(j, Multiply(k, d))), c))));
        var starts = Seq(OpenBrace, j, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Parenthesized(run), CloseBrace);
        return Disp(Bind(FormulaQuantifier.ForAll, "d", Naturals(),
            Equal(Call("goldenMAPFirstStart", d), Call("sInf", starts))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var twice = Multiply(D(2), n);
        var odd = Equal(Call("goldenMAPFirstStart", Call("fib", Add(twice, D(1)))),
            Subtract(Call("fib", Add(twice, D(3))), D(2)));
        var even = Equal(Call("goldenMAPFirstStart", Call("fib", twice)),
            Subtract(Call("fib", Multiply(D(4), n)), D(1)));
        return Disp(Bind(FormulaQuantifier.ForAll, "n", Naturals(),
            Implies(AtMost(D(1), n), Parenthesized(And(odd, even)))));
    }

    private static Formula OpenRotationRunFormula()
    {
        var lo = F.Id("lo"); var hi = F.Id("hi"); var eps = F.Id("eps");
        var x = F.Id("x"); var length = F.Id("length");
        var forward = F.Id("forward"); var k = F.Id("k");
        var zero = D(0); var one = D(1);
        var width = Subtract(hi, lo);
        var steps = Parenthesized(Seq(Subtract(length, one), Colon, Naturals()));
        var choice = Seq(Operatorname, Grp(F.Id("if")), Sp, forward, Sp,
            Operatorname, Grp(F.Id("then")), Sp, eps, Sp,
            Operatorname, Grp(F.Id("else")), Sp, new Formula.Negate(eps));
        var sign = Seq(Operatorname, Grp(F.Id("if")), Sp, forward, Sp,
            Operatorname, Grp(F.Id("then")), Sp, Parenthesized(Seq(one, Colon, Reals())), Sp,
            Operatorname, Grp(F.Id("else")), Sp, new Formula.Negate(one));
        var memory = Bind(FormulaQuantifier.ForAll, "k", Naturals(),
            Implies(Less(k, length), Parenthesized(And(
                Less(lo, new Formula.Apply(x, [k])),
                Less(new Formula.Apply(x, [k]), hi)))));
        var orbit = Bind(FormulaQuantifier.ForAll, "k", Naturals(),
            Implies(Less(Add(k, one), length), Equal(
                new Formula.Apply(x, [Add(k, one)]),
                new Formula.Apply(Seq(Operatorname, Grp(F.Id("Int")), Dot,
                    Operatorname, Grp(F.Id("fract"))),
                    [Add(new Formula.Apply(x, [k]), Parenthesized(choice))]))));
        var conclusion = And(
            Equal(new Formula.Apply(x, [Subtract(length, one)]),
                Add(new Formula.Apply(x, [zero]),
                    Multiply(Multiply(Parenthesized(sign), steps), eps))),
            Less(Multiply(steps, eps), width));
        Formula body = Parenthesized(conclusion);
        foreach (var premise in new[] { orbit, memory, Less(zero, length),
            AtMost(eps, Subtract(one, Parenthesized(width))), AtMost(hi, one),
            AtMost(zero, lo), Less(zero, eps) })
            body = Implies(Parenthesized(premise), Parenthesized(body));
        body = Bind(FormulaQuantifier.ForAll, "forward", F.Id("Bool"), body);
        body = Bind(FormulaQuantifier.ForAll, "length", Naturals(), body);
        body = Bind(FormulaQuantifier.ForAll, "x", Seq(Naturals(), Sp, To, Sp, Reals()), body);
        body = Bind(FormulaQuantifier.ForAll, "eps", Reals(), body);
        body = Bind(FormulaQuantifier.ForAll, "hi", Reals(), body);
        return Disp(Bind(FormulaQuantifier.ForAll, "lo", Reals(), body));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable,
        Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
