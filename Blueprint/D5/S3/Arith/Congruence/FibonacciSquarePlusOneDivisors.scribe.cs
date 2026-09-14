using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class FibonacciSquarePlusOneDivisorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/FibonacciSquarePlusOneDivisors.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The non-unit Fibonacci divisors of a Fibonacci square plus one have exactly "
            + "the indices dividing one of two explicitly determined neighbouring indices.",
        H("Exact Fibonacci Divisors of Square-Plus-One Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-fibonacci-square-divisor-indices"),
                DeclarationHandle.Create(Prefix + "even_square_plus_one_divisors"),
                H("Every even centre at least two"),
                StatementSource.FromAuthor(EvenFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all natural m and k with k at least three, F(k) divides "
                            + "F(2*m+2)^2+1 exactly when k divides 2*m+1 or 2*m+3. "
                            + "The original golden norm gives the Cassini factorization. "
                            + "The integer gcd-product divisibility identity and Fibonacci "
                            + "strong divisibility then rule out splitting a full Fibonacci "
                            + "divisor between the two factors.")),
                    Paragraph(Text(
                        "The value one is deliberately outside the k>=3 endpoint: "
                            + "F(1)=F(2)=1 is a single positive divisor value. The smallest "
                            + "centre m=0 is included. No primality or WSS assumption "
                            + "occurs in the statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-fibonacci-square-divisor-indices"),
                DeclarationHandle.Create(Prefix + "odd_square_plus_one_divisors"),
                H("Every odd centre at least three"),
                StatementSource.FromAuthor(OddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all natural m and k with k at least three, F(k) divides "
                            + "F(2*m+3)^2+1 exactly when k divides 2*m+1 or 2*m+5. "
                            + "Here Cassini together with the recurrence moves the "
                            + "two factors to offsets minus two and plus two.")),
                    Paragraph(Text(
                        "The private two-factor engine does not require the factors "
                            + "to be coprime. If neither index is divisible by k, both "
                            + "gcd indices are at most floor(k/2), yet their Fibonacci "
                            + "product is strictly smaller than F(k). These two endpoints "
                            + "describe the full non-unit divisor-index spectra. The "
                            + "separate divisor-count formula, the Lucas factor-five "
                            + "classification, and the WSS zero-block descent are not "
                            + "additional Lean declarations in this document."))),
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
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula Index(int offset) =>
        Call("add", Call("mul", V("2"), V("m")), V(offset.ToString()));
    private static Formula Fib(Formula n) => Call("Nat.fib", n);
    private static Formula Target(int offset) =>
        Call("add", new Formula.Power(Fib(Index(offset)), V("2")), V("1"));
    private static Formula Spectrum(int centre, int left, int right) =>
        Disp(All("m", All("k", Call("Implies", Call("Le", V("3"), V("k")),
            Call("Iff", Call("Dvd", Fib(V("k")), Target(centre)),
                Call("Or", Call("Dvd", V("k"), Index(left)),
                    Call("Dvd", V("k"), Index(right))))))));
    private static Formula EvenFormula() => Spectrum(2, 1, 3);
    private static Formula OddFormula() => Spectrum(3, 1, 5);
}
