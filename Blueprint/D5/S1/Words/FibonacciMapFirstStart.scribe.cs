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
                DescribeRole.Theorem))));

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

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
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
