using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class PrimeZeckendorfFrequencyBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/EulerGerm/PrimeZeckendorfFrequencyBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeckendorf long-short layer steps become logarithmically prime-scaled frequency gaps in the golden heat spectrum.",
        H("Prime-Zeckendorf Frequency Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorf-selects-prime-frequency-gap"),
                DeclarationHandle.Create(Prefix + "zeckendorf_selects_prime_frequency_gap"),
                H("Zeckendorf selects the prime-local frequency gap"),
                StatementSource.FromAuthor(ZeckendorfFrequencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Within a fixed prime channel, absence of Fibonacci index two selects the long phi-squared times log p increment, while presence selects the short phi times log p increment.")),
                    Paragraph(Text(
                        "The theorem composes the existing Zeckendorf beta-gap bridge with the separable golden heat energy beta(v) log p. Frequency here is an analytic heat-energy coordinate, not a claim that a projection layer is itself one physical frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-prime-frequency-gap-balance"),
                DeclarationHandle.Create(Prefix + "cross_prime_frequency_gap_balance"),
                H("Prime channels share one golden symbolic increment"),
                StatementSource.FromAuthor(CrossPrimeBalanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "After cross-multiplication by the logarithmic prime coordinates, consecutive frequency gaps agree across any two prime channels.")),
                    Paragraph(Text(
                        "This proves separability of prime scale and golden depth. It supplies no canonical geometric identification of the prime labels, which remains blocked by prime-relabeling symmetry."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Frequency(Formula prime, Formula layer) =>
        Call("primeLayerFrequency", prime, layer);

    private static Formula WDigits(Formula layer) => Call("wdigits", layer);

    private static Formula LogPrime(Formula prime) =>
        Seq(Log, Open, prime, Close);

    private static Formula Gap(Formula prime, Formula layer) =>
        Seq(
            Frequency(prime, Seq(layer, Plus, D(1))),
            Sp, Minus, Sp,
            Frequency(prime, layer));

    private static Formula ZeckendorfFrequencyFormula()
    {
        Formula prime = F.Id("p");
        Formula layer = F.Id("v");
        Formula longGap = Seq(
            Gap(prime, layer), Sp, Eq, Sp,
            Varphi, Caret, Grp(D(2)), Sp, Times, Sp, LogPrime(prime));
        Formula shortGap = Seq(
            Gap(prime, layer), Sp, Eq, Sp,
            Varphi, Sp, Times, Sp, LogPrime(prime));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Colon, Sp, F.Id("Nat.Primes"), Comma, Sp,
            layer, InMacro, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            Open,
            Neg, Open, D(2), Sp, InMacro, Sp, WDigits(layer), Close,
            Sp, Rightarrow, Sp, longGap,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            D(2), Sp, InMacro, Sp, WDigits(layer),
            Sp, Rightarrow, Sp, shortGap,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CrossPrimeBalanceFormula()
    {
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        Formula layer = F.Id("v");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, F.Id("Nat.Primes"),
            Comma, Sp, layer, InMacro, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            LogPrime(second), Sp, Times, Sp, Open, Gap(first, layer), Close,
            Sp, Eq, Sp,
            LogPrime(first), Sp, Times, Sp, Open, Gap(second, layer), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
