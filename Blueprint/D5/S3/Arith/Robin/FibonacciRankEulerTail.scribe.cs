using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FibonacciRankEulerTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primes with one Fibonacci entry index have a harmonic Euler logarithm bound.",
        H("Fibonacci Rank Euler Tail"),
        Blocks(
            Paragraph(Text("For a natural index d, B(d) is the finite set of prime "
                + "divisors p of F(d) such that p divides no F(k) with 1 <= k < d. "
                + "Thus B(d) contains every prime with first positive Fibonacci zero "
                + "at d, with each prime counted once. H(d) is the sum of 1/k for "
                + "1 <= k <= d.")),
            Describe.Lean(
                DescribeId.Create("rank-bucket-euler-logarithm-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/FibonacciRankEulerTail.result"),
                H("Complete prime bucket bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The index d is any natural number greater than five. "
                        + "The sum ranges over the whole bucket, counting each prime "
                        + "once without a cutoff on its size.")),
                    Paragraph(Text("The product of the distinct bucket primes divides "
                        + "F(d), so the number of primes is less than d. The Fibonacci "
                        + "rank theorem places every prime in one of the progressions "
                        + "k*d+1 and k*d-1. Primes at most d squared contribute at most "
                        + "4*H(d)/d, while all larger primes contribute at most 1/d. "
                        + "The harmonic number bound gives the second inequality.")),
                    Paragraph(Text("This estimates logarithms of Euler factors for one "
                        + "entry index. It makes no Robin inequality or Riemann hypothesis "
                        + "claim."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula d = F.Id("d");
        Formula p = F.Id("p");
        Formula hd = new Formula.Apply(F.Id("H"), [d]);
        Formula bucket = new Formula.Apply(F.Id("B"), [d]);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(p, Sp, InMacro, Sp, bucket)), Sp,
            new Formula.Apply(Log, [new Formula.Fraction(p, Seq(p, Minus, D(1)))]));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, d, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                Sp, D(5), Sp, Lt, Sp, d, Sp, Rightarrow),
            Seq(sum, Sp, Le, Sp, new Formula.Fraction(Seq(D(6), hd), d),
                Sp, Le, Sp, new Formula.Fraction(
                    Seq(D(6), Open, D(1), Plus, new Formula.Apply(Log, [d]), Close), d))
        ]));
    }
}
