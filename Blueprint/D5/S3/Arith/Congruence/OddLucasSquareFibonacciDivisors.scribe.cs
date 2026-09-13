using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class OddLucasSquareFibonacciDivisorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/OddLucasSquareFibonacciDivisors.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At odd indices the Fibonacci divisors of the existing Lucas trace squared plus one "
            + "are exactly one or the pair one and two. This proves both numbered conjectures "
            + "in OEIS A339669 through one classification theorem.",
        H("Odd Lucas Squares and Fibonacci Divisors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-lucas-fibonacci-divisor-rigidity"),
                DeclarationHandle.Create(Prefix + "fibonacci_divisor_dvd_two"),
                H("Every Fibonacci divisor lies in one fixed two-element set"),
                StatementSource.FromAuthor(DivisorBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every odd natural n and every natural k, if F(k) "
                        + "divides L(n)^2+1, then F(k) divides 2. Here L is the existing "
                        + "goldenLucas trace, and target is its positive square plus one "
                        + "converted to a natural number with an explicit cast equality.")),
                    Paragraph(Text("The proof derives F(3*n)=F(n)*(L(n)^2+1) from the cube "
                        + "coefficient of the original GoldenInt ring. The Pell identity "
                        + "gives L(n)^2+4=5*F(n)^2. Oddness and strong Fibonacci "
                        + "divisibility show gcd(F(n),3)=1, hence gcd(F(n),L(n)^2+1)=1.")),
                    Paragraph(Text("A hypothetical Fibonacci divisor therefore has index "
                        + "coprime to n. Strong divisibility puts its value inside "
                        + "F(gcd(k,3*n)); the index of that last number divides 3. "
                        + "Thus the original divisor divides F(3)=2. The ambiguity "
                        + "F(1)=F(2)=1 is treated explicitly rather than ignored."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a339669-conjecture-one"),
                DeclarationHandle.Create(Prefix + "lagneau_conjecture_one"),
                H("Lagneau's first conjecture"),
                StatementSource.FromAuthor(FirstClaim()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural t, a339669(6*t+3)=1. The count is "
                        + "the cardinality of a finite SET of positive divisors which "
                        + "are Fibonacci values. The two indices representing the value "
                        + "one do not contribute two divisors.")),
                    Paragraph(Text("External anchor: Michel Lagneau, OEIS A339669, "
                        + "Conjecture 1, December 12, 2020, https://oeis.org/A339669 . "
                        + "The fetched entry retained the conjecture label. This binding "
                        + "does not assert that a complete historical literature audit "
                        + "or Lean compilation has been performed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a339669-conjecture-two"),
                DeclarationHandle.Create(Prefix + "lagneau_conjecture_two"),
                H("Lagneau's second conjecture, as one joint claim"),
                StatementSource.FromAuthor(SecondClaim()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural t, a339669(6*t+1)=2 and "
                        + "a339669(6*t+5)=2. odd_fibonacci_divisors proves the stronger "
                        + "set equality: the divisor set is {1} when 3 divides the "
                        + "odd index and {1,2} otherwise. The parity step is derived "
                        + "from the same identities and F(3)=2.")),
                    Paragraph(Text("External anchor: the separately numbered Conjecture 2 "
                        + "in the same OEIS entry. Its two residue classes remain one "
                        + "claim. The first and second conjectures are two external "
                        + "statements settled by one proof family, not two independent "
                        + "discoveries. No result on the unrestricted even-index count "
                        + "or Wall-Sun-Sun existence is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula DivisorBound() => Disp(Call("Implies",
        Call("Divides", Call("F", F.Id("k")), Call("target", F.Id("n"))),
        Call("Divides", Call("F", F.Id("k")), F.Id("2"))));

    private static Formula FirstClaim() => Disp(Seq(
        Call("a", Call("add", Call("mul", F.Id("6"), F.Id("t")), F.Id("3"))),
        Sp, Eq, Sp, F.Id("1")));

    private static Formula SecondClaim() => Disp(Call("And",
        Call("Eq", Call("a", Call("add", Call("mul", F.Id("6"), F.Id("t")), F.Id("1"))), F.Id("2")),
        Call("Eq", Call("a", Call("add", Call("mul", F.Id("6"), F.Id("t")), F.Id("5"))), F.Id("2"))));
}
