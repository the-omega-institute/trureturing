using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GoldenEulerGapWordConstraintsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenEulerGapWordConstraints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The deterministic golden Euler frequency word forbids two consecutive short steps "
            + "and three consecutive long steps, and Euler phase letters inherit the same grammar.",
        H("Golden Euler Gap Word Constraints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("short-frequency-forces-next-long"),
                DeclarationHandle.Create(Prefix + "short_frequency_forces_next_long"),
                H("A short frequency step forces a following long step"),
                StatementSource.FromAuthor(ShortForcesLongFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden word identifies true letters with phi-squared prime-log "
                            + "gaps and false letters with phi prime-log gaps. Existing golden "
                            + "desubstitution proves that false-false never occurs, so every "
                            + "short frequency letter is followed by a long one.")),
                    Paragraph(Text(
                        "The same module proves that three long letters never occur and transports "
                            + "both forbidden-word laws to the Euler phase alphabet. This is a "
                            + "deterministic symbolic constraint; an explicit stochastic non-iid "
                            + "theorem would additionally require a chosen probability measure."))),
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

    private static Formula GapAt(Formula prime, Formula layer) =>
        Seq(
            Frequency(prime, Seq(layer, Plus, D(1))),
            Sp, Minus, Sp,
            Frequency(prime, layer));

    private static Formula ShortForcesLongFormula()
    {
        Formula prime = F.Id("p");
        Formula layer = F.Id("v");
        Formula logPrime = Seq(Log, Open, prime, Close);
        return Disp(Seq(
            Forall, Sp, prime, Colon, Sp, F.Id("Nat"), Dot, F.Id("Primes"), Comma, Sp,
            Forall, Sp, layer, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Call("goldenWord", layer), Sp, Eq, Sp, Operatorname, Grp(F.Id("false")), Sp, Rightarrow, Sp,
            Open,
            GapAt(prime, layer), Sp, Eq, Sp, Varphi, Sp, Times, Sp, logPrime,
            Close,
            Sp, Land, Sp,
            Open,
            GapAt(prime, Seq(layer, Plus, D(1))), Sp, Eq, Sp,
            Varphi, Caret, Grp(D(2)), Sp, Times, Sp, logPrime,
            Close, Dot));
    }
}
