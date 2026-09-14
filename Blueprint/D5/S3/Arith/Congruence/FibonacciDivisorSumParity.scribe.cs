using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class FibonacciDivisorSumParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/FibonacciDivisorSumParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite set of distinct positive Fibonacci values containing one can sum to a "
            + "Fibonacci value only in one alternating shape. Applied to actual divisor "
            + "sets, this proves the conjecture in OEIS A339621 for every natural input.",
        H("Fibonacci Divisor Sums and Forced Index Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("anchored-fibonacci-pattern"),
                DeclarationHandle.Create(Prefix + "alternatingIndices"),
                H("The forced finite index pattern"),
                StatementSource.FromAuthor(PatternFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural r, the index pattern is {0} together with "
                        + "{2*j+1: 0 <= j < r}. Index i denotes the value F(i+2). "
                        + "Thus r=0 gives the singleton value one, and r=2 gives "
                        + "the values {1,2,5}. The two Fibonacci indices for one "
                        + "do not create two different terms."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fibonacci-divisor-set"),
                DeclarationHandle.Create(Prefix + "fibonacciDivisors"),
                H("Actual distinct divisor values"),
                StatementSource.FromAuthor(DivisorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural N, take Nat.divisors N and retain exactly "
                        + "those values equal to Nat.fib n for some natural n. "
                        + "This is a finite set of divisor values. The theorems "
                        + "below require N>0, so zero is not a divisor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fibonacci-divisor-sum"),
                DeclarationHandle.Create(Prefix + "fibonacciDivisorSum"),
                H("Sum with one counted once"),
                StatementSource.FromAuthor(SumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum is over the actual finite divisor set, with summand d. "
                        + "It is neither a sum over all Fibonacci indices nor a sum "
                        + "over a supplied finite approximation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-containing-fibonacci-classification"),
                DeclarationHandle.Create(Prefix + "one_containing_fibonacci_sum"),
                H("Complete classification of one-containing sums"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite set s of natural indices containing zero "
                            + "and every natural n, sum(i in s) F(i+2)=F(n+2) "
                            + "if and only if n=2*r and s=alternatingIndices r for "
                            + "some natural r. There is no nonadjacency, divisor, "
                            + "modulo-three or square-plus-one hypothesis.")),
                    Paragraph(Text(
                        "The sum of all distinct smaller values except the immediate "
                            + "predecessor is two below the target. Thus the predecessor "
                            + "is forced. Removing it preserves the term one and reduces "
                            + "the target index by two. The initial value one is permitted; "
                            + "the value two has no such representation. Strong induction "
                            + "gives the forced alternating shape, and the recurrence "
                            + "proves the converse sum identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-moduli-fibonacci-divisor-rigidity"),
                DeclarationHandle.Create(Prefix + "fibonacci_divisor_sum_rigidity"),
                H("All positive integers, with the exact divisor set"),
                StatementSource.FromAuthor(AllModuliFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural N, if its Fibonacci-divisor sum "
                            + "is any Fibonacci value, there is a natural r such that "
                            + "the sum is F(2*r+2) and the full divisor set is the image "
                            + "of alternatingIndices r under i |-> F(i+2). The finite "
                            + "index carrier used in the proof is proved complete by "
                            + "i < F(i+2) <= N, and strict Fibonacci monotonicity proves "
                            + "that the value map is injective.")),
                    Paragraph(Text(
                        "In ordinary indexing, the resulting divisor set is "
                            + "{1,F(3),F(5),...,F(2*r+1)}. This general positive-N "
                            + "classification is the single proof family containing "
                            + "the externally stated square-plus-one conjecture."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a339621-conjecture"),
                DeclarationHandle.Create(Prefix + "a339621_conjecture"),
                H("Lagneau's A339621 conjecture"),
                StatementSource.FromAuthor(OeisFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural m, if the sum of distinct Fibonacci "
                            + "divisors of m^2+1 is a Fibonacci number, then it equals "
                            + "F(2*r) for some positive natural r. The value one is "
                            + "represented as F(2); it also equals F(1), so the theorem "
                            + "asserts existence of an even index rather than declaring "
                            + "every possible representing index even.")),
                    Paragraph(Text(
                        "External statement: Michel Lagneau, OEIS A339621, "
                            + "December 10, 2020. Its definition counts the divisor "
                            + "one only once. The general classification does not "
                            + "assert that every even-index Fibonacci value occurs "
                            + "for some input, nor that a WSS prime exists."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula body) =>
        Seq(Exists, Sp, V(name), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("mul", a, b);
    private static Formula Fib(Formula n) => Call("Nat.fib", n);
    private static Formula Pattern() => Call("alternatingIndices", V("r"));
    private static Formula Divisors(Formula n) => Call("fibonacciDivisors", n);
    private static Formula Total(Formula n) => Call("fibonacciDivisorSum", n);
    private static Formula IsFib(Formula value) => Ex("n", Eqn(value, Fib(V("n"))));
    private static Formula ImagePattern() => Call("image", Call("lambda", V("i"),
        Fib(Add(V("i"), V("2")))), Pattern());

    private static Formula PatternFormula() => Disp(All("r", NatType(), Eqn(Pattern(),
        Call("insert", V("0"), Call("image", Call("lambda", V("j"),
            Add(Mul(V("2"), V("j")), V("1"))), Call("range", V("r")))))));
    private static Formula DivisorsFormula() => Disp(All("N", NatType(), Eqn(Divisors(V("N")),
        Call("filter", Call("lambda", V("d"), IsFib(V("d"))), Call("Nat.divisors", V("N"))))));
    private static Formula SumFormula() => Disp(All("N", NatType(), Eqn(Total(V("N")),
        Call("sum", Divisors(V("N")), Call("lambda", V("d"), V("d"))))));
    private static Formula ClassificationFormula() => Disp(All("s", Call("Finset", NatType()),
        All("n", NatType(), Call("Implies", Call("Mem", V("0"), V("s")),
            Call("Iff", Eqn(Call("sum", V("s"), Call("lambda", V("i"),
                Fib(Add(V("i"), V("2"))))), Fib(Add(V("n"), V("2")))),
                Ex("r", Call("And", Eqn(V("n"), Mul(V("2"), V("r"))),
                    Eqn(V("s"), Pattern()))))))));
    private static Formula AllModuliFormula() => Disp(All("N", NatType(),
        Call("Implies", Call("And", Call("Lt", V("0"), V("N")), IsFib(Total(V("N")))),
            Ex("r", Call("And", Eqn(Total(V("N")), Fib(Add(Mul(V("2"), V("r")), V("2")))),
                Eqn(Divisors(V("N")), ImagePattern()))))));
    private static Formula OeisFormula()
    {
        var target = Add(new Formula.Power(V("m"), V("2")), V("1"));
        return Disp(All("m", NatType(), Call("Implies", IsFib(Total(target)),
            Ex("r", Call("And", Call("Lt", V("0"), V("r")),
                Eqn(Total(target), Fib(Mul(V("2"), V("r")))))))));
    }
}
