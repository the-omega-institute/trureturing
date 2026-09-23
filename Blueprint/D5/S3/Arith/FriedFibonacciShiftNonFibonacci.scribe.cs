using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FriedFibonacciShiftNonFibonacciDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FriedFibonacciShiftNonFibonacci.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/fried2025proofs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No Fibonacci number equals the n-th Fibonacci number plus 2n plus one times the next "
            + "one.",
        H("A Shifted Fibonacci Combination That Is Never Fibonacci"),
        Blocks(
            Node("conjecture-statement", "The conjectured non-representation", "claim",
                ClaimFormula(),
                "The closing paragraph of Section 6 of the source reads verbatim: \"Nevertheless, "
                    + "we were not able to show that the two sets, the set of n times F of n over "
                    + "two plus three minus n minus one times F of n over two plus two for n at "
                    + "least one even, and the set of F of n plus one over two plus two for n at "
                    + "least one odd, are disjoint, or, equivalently, that for every n in N, the "
                    + "number F of n plus two plus two n times F of n plus one is not a Fibonacci "
                    + "number. We conjecture that this is so.\" The source indexes the Fibonacci "
                    + "numbers so that the first and second are both one, which is the indexing "
                    + "displayed here. Both of its two sets are indexed from one, so the natural "
                    + "numbers of the equivalent form start at one; at zero the number would be "
                    + "the second Fibonacci number itself, while the two sets are unchanged. "
                    + "Writing the even index as twice j turns the first set into the numbers "
                    + "displayed here, since twice j times the difference of two consecutive "
                    + "Fibonacci numbers is twice j times the earlier one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-proved", "The conjectured non-representation holds", "result",
                ResultFormula(),
                "Write X for the number in question. The recurrence rewrites it as the n-th "
                    + "Fibonacci number plus two n plus one times the next one. Suppose some "
                    + "Fibonacci number with index m equals X. For n at most seven the values of "
                    + "X are four, eleven, twenty-three, forty-eight, ninety-three, one hundred "
                    + "seventy-seven and three hundred twenty-eight, all below the fourteenth "
                    + "Fibonacci number, which is three hundred seventy-seven; monotonicity "
                    + "bounds m below fourteen and the finitely many remaining pairs are "
                    + "excluded by evaluation. For n at least eight, X is at least three times "
                    + "the Fibonacci number of index n plus one, so m is at least n plus two; "
                    + "write m as j plus n plus one with j at least one. The addition formula "
                    + "expresses the Fibonacci number of index j plus n plus one as F of j times "
                    + "F of n plus F of j plus one times F of n plus one, so the supposed "
                    + "equality becomes an equation between two such combinations. Since F of j "
                    + "is at least one, the coefficient F of j plus one is at most two n plus "
                    + "one, and the equation rearranges, with subtraction staying inside the "
                    + "natural numbers, to F of j minus one times F of n equals two n plus one "
                    + "minus F of j plus one times F of n plus one. If F of j equals one then j "
                    + "is at most two and F of j plus one is at most two, whereas cancelling the "
                    + "positive factor F of n from the original equation forces F of j plus one "
                    + "to equal two n plus one, which is at least seventeen. Otherwise F of j is "
                    + "at least two, so F of j minus one is positive. The rearranged identity "
                    + "shows that F of n plus one divides F of j minus one times F of n, and "
                    + "consecutive Fibonacci numbers are coprime, so F of n plus one divides F of "
                    + "j minus one and is therefore at most it. The left side of the identity is "
                    + "then at least F of n plus one times F of n, while its right side is at "
                    + "most two n times F of n plus one because F of j plus one is positive. "
                    + "Cancelling the positive factor F of n plus one gives F of n at most two n. "
                    + "That contradicts two n below F of n for n at least eight, which holds at "
                    + "eight because the eighth Fibonacci number is twenty-one, and propagates "
                    + "because each step adds a Fibonacci number of index at least seven, hence "
                    + "at least thirteen.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fried-fibonacci-shift-non-fibonacci"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Fib(Formula argument) => Call("fib", argument);

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var target = Add(Fib(Add(n, D(2))),
            Multiply(Multiply(D(2), n), Fib(Add(n, D(1)))));
        var inner = Universal("m", Naturals(), NotEqual(Fib(m), target));
        var body = Universal("n", Naturals(), Implies(LessEqual(D(1), n), inner));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
