using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class NormOneCriticalPrimesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/NormOneCriticalPrimes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the actual norm-one Lucas recurrence, prime fixed points are exactly the prime "
            + "divisors of a-2. A mixed fixed modulus refutes the literal positive-parameter "
            + "clause (v) of Benfield-Lippard Conjecture 6.5.",
        H("Norm-One Critical Primes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-one-prime-fixed-classification"),
                DeclarationHandle.Create(Prefix + "prime_fixed_iff_dvd_parameter_sub_two"),
                H("Exact classification at every prime"),
                StatementSource.FromAuthor(PrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every integer a and prime p, period(a,p)=p "
                        + "exactly when p divides a-2. period is the existing LucasCompanion "
                        + "matrixPeriod at parameters a and q=1, corresponding to "
                        + "U(n+2)=a*U(n+1)-U(n), U(0)=0, U(1)=1. "
                        + "period_dvd_iff_sequence identifies the entire sequence period.")),
                    Paragraph(Text("Necessity uses the finite-field trace-of-pth-power "
                        + "identity. Sufficiency uses the actual power matrix at parameter "
                        + "two: [[t+1,-t],[t,1-t]]. Its lower-left entry proves minimality. "
                        + "The prime two is included. The classification is classical "
                        + "linear algebra, not independently counted as an open problem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("benfield-lippard-conjecture65v-refutation"),
                DeclarationHandle.Create(Prefix + "refutes_conjecture65v"),
                H("A mixed fixed modulus contradicts the stated necessary forms"),
                StatementSource.FromAuthor(Call("Not", F.Id("conjecture65vNecessary"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The external claim's positive a=-1 mod 6 case permits "
                        + "a prime power or a number divisible by six. Our predicate is "
                        + "a weaker necessary condition allowing any prime, rather than "
                        + "only prime divisors of a squared minus four. The witness is "
                        + "a=47 and m=15: the period is 15, but 15 is neither a prime "
                        + "power nor divisible by six.")),
                    Paragraph(Text("mixed_fixed_family proves the same fixed modulus for "
                        + "every a=47+30*t. witness_is_golden_trace identifies 47 with "
                        + "the existing goldenLucas(8). The recurrence has norm one; "
                        + "this result is not a classical Fibonacci Wall-Sun-Sun prime.")),
                    Paragraph(Text("Source: Benfield and Lippard, Fixed Points of K-Fibonacci "
                        + "Sequences, arXiv:2404.08194v2, Section 6, Conjecture 6.5(v) "
                        + "and the following critical-prime question. The formal target "
                        + "is the literal necessary consequence displayed above, not a "
                        + "classification of all fixed moduli or a refutation of the "
                        + "paper's proved positive-sign K-Fibonacci results. "
                        + "Priority and the interpretation of a possible source typo "
                        + "remain subject to external confirmation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula PrimeFormula() => Disp(Call("Implies", Call("Prime", F.Id("p")),
        Call("Iff", Call("Eq", Call("period", F.Id("a"), F.Id("p")), F.Id("p")),
            Call("Divides", F.Id("p"), Call("Sub", F.Id("a"), D(2))))));
}
