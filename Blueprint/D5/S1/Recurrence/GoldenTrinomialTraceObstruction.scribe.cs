using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenTrinomialTraceObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GoldenTrinomialTraceObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power-compositional trinomial evaluated at the original golden unit has "
            + "the exact scalar obstruction L(n)-1 at every odd index and every modulus.",
        H("Golden Trinomial and Prime-Index Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-trinomial-trace-factor"),
                DeclarationHandle.Create(Prefix + "evaluatedDefect_factor"),
                H("Exact evaluated factorization"),
                StatementSource.FromAuthor(FactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every odd natural n, compositionalTrinomial(n) "
                        + "is the actual integer polynomial X^(2*n)-X^n-1. "
                        + "evaluatedDefect(n) evaluates it at the existing GoldenInt.phi. "
                        + "The result is (goldenLucas(n)-1)*phi^n. "
                        + "The proof uses trace, norm and the integral quadratic relation.")),
                    Paragraph(Text("Oddness is essential: norm(phi^n)=-1 in this branch. "
                        + "defect_norm proves the norm is -(goldenLucas(n)-1)^2. "
                        + "This is an exact identity, not a numerical approximation "
                        + "based on growth of the positive real embedding."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-trinomial-scalar-obstruction"),
                DeclarationHandle.Create(Prefix + "scalar_divisibility_iff"),
                H("The scalar divisibility obstruction is completely preserved"),
                StatementSource.FromAuthor(DivisibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every integer q and odd natural n, q divides "
                        + "evaluatedDefect(n) in GoldenInt exactly when q divides "
                        + "goldenLucas(n)-1 in the integers. An explicit inverse "
                        + "-conj(phi^n) performs the cancellation before any reduction.")),
                    Paragraph(Text("reduced_defect_zero_iff uses the existing GoldenMod "
                        + "and applies to every natural modulus. prime_square_test "
                        + "specializes to p squared at odd prime p, including 5. "
                        + "No claim identifying the number-field order index is assumed "
                        + "or formalized by this source.")),
                    Paragraph(Text("Research anchor: Jones, A new condition for "
                        + "k-Wall-Sun-Sun primes, arXiv:2302.10357v4, Theorem 1.1 "
                        + "and Lemmas 3.4-3.5, specialized to k=1. "
                        + "This adapter is known-theory formalization, not a new "
                        + "solution of WSS existence or a new independent open problem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula FactorFormula() => Disp(Call("Implies", Call("Odd", F.Id("n")),
        Call("Eq", Call("evaluatedDefect", F.Id("n")),
            Seq(Call("traceExcess", F.Id("n")), Cdot, Call("power", F.Id("phi"), F.Id("n"))))));

    private static Formula DivisibilityFormula() => Disp(Call("Implies", Call("Odd", F.Id("n")),
        Call("Iff", Call("DividesInGoldenInt", F.Id("q"), Call("evaluatedDefect", F.Id("n"))),
            Call("DividesInInt", F.Id("q"), Call("traceExcess", F.Id("n"))))));
}
