using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciFrobeniusQuotientBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciFrobeniusQuotientBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The existing golden Frobenius theorem supplies the standard p-(5/p) Fibonacci zero. When the actual return period is identified with that index, the two normalized quotients agree exactly. The coefficient is 1 and therefore a unit.",
            H("Fibonacci Frobenius Quotient Bridge"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("quotient-period-eq-frobenius"),
                    DeclarationHandle.Create(Prefix + "quotient_period_eq_frobenius"),
                    H("Conditional exact identification of the two normalized quotients"),
                    StatementSource.FromAuthor(BridgeFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a prime p different from 2 and 5, assume the actual least return period equals the standard Frobenius index p minus the absolute value of the Legendre symbol (5/p). The normalized quotient at the return period is then exactly the normalized quotient at the Frobenius index, with proportionality coefficient 1.")),
                        Paragraph(Text(
                            "This is deliberately conditional. The current repository proves the Frobenius zero and the rank divisibility bound, but does not yet prove that every return period is the Frobenius index or derive a nontrivial Lucas multiplier for an arbitrary multiple."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("quotient-period-eq-frobenius-factor-isUnit"),
                    DeclarationHandle.Create(Prefix + "quotient_period_eq_frobenius_factor_isUnit"),
                    H("The proportionality factor is invertible"),
                    StatementSource.FromAuthor(UnitFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The coefficient is 1 in ZMod(p), so it is a unit for every prime, including p=2 and p=5. The exceptional primes are excluded only from the Frobenius-index identification theorem, not from this unit fact."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("frobenius-index-fib-dvd"),
                    DeclarationHandle.Create(Prefix + "frobenius_index_fib_dvd"),
                    H("The Frobenius index is an actual p-divisible Fibonacci index"),
                    StatementSource.FromAuthor(DvdFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every prime other than 5, the existing golden Frobenius apparition theorem supplies p dividing F at the standard index. The proof converts the signed Legendre index to its natural-number form and preserves p=2 as a valid apparition case."))),
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

    private static Formula BridgeFormula() => Disp(Call("Eq",
        Call("quotientMod", F.Id("p"), Call("period", F.Id("p"))),
        Seq(F.Id("1"), Cdot, Call("quotientMod", F.Id("p"),
            Call("frobeniusIndex", F.Id("p"))))));

    private static Formula UnitFormula() => Disp(Call("IsUnit", F.Id("1")));

    private static Formula DvdFormula() => Disp(Call("Dvd",
        F.Id("p"), Call("F", Call("frobeniusIndex", F.Id("p")))));
}
