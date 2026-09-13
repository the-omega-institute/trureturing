using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenPrimePowerDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GoldenPrimePowerDepth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primitive golden-integer defect gains exactly one p-adic depth per p-th power. "
            + "This determines its exact order at every finer modulus.",
        H("Golden Prime-Power Defect Depth"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-prime-power-exact-order"),
            DeclarationHandle.Create(Prefix + "reduced_order_at_depth"),
            H("Exact order from a primitive seed"),
            StatementSource.FromAuthor(OrderFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let p be prime, s>0, s+2<=p*s, and B a golden integer "
                    + "not divisible by the ordinary scalar p. Set gamma=1+p^s*B. "
                    + "For every natural j, the reduction of gamma modulo p^(s+j) "
                    + "has order exactly p^j.")),
                Paragraph(Text("The proof reuses mathlib's generic "
                    + "ZMod.exists_one_add_mul_pow_prime_pow_eq with coefficient ring GoldenInt. "
                    + "It constructs gamma^(p^j)=1+p^(s+j)*(B+p*C). "
                    + "The residue of B+p*C is still primitive. Scalar cancellation is "
                    + "proved in the integer coordinates, not in a residue ring.")),
                Paragraph(Text("The stability inequality permits all s>=1 for odd primes "
                    + "and requires s>=2 at p=2. seeded_period_all combines this depth "
                    + "result with an actual old period and proves both the plateau "
                    + "and growth regimes. FibonacciPrimePowerPeriod constructs the "
                    + "seed from the valuation of the actual return content, so the "
                    + "final Fibonacci theorem does not assume an unknown lifting law."))),
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

    private static Formula OrderFormula() => Disp(Seq(
        Call("orderOf", Call("reduce", Call("power", F.Id("p"),
            Seq(F.Id("s"), Plus, F.Id("j"))), F.Id("gamma"))),
        Sp, Eq, Sp, Call("power", F.Id("p"), F.Id("j"))));
}
