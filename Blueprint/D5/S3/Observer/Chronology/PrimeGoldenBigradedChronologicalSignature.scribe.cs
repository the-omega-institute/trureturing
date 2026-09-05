using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenBigradedChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-factor count and Zeckendorf-selected short-step count form an additive bigrading beside the chronological Hopf signature.",
        H("Prime-Golden Bigraded Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-bigraded-time-reversal"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_bigraded_time_reversal_laws"),
                H("Bigrading survives reversal while Magnus orientation flips"),
                StatementSource.FromAuthor(TimeReversalLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Chronological concatenation multiplies the step-two signature and adds two unsigned degrees: prime-event count with multiplicity and the count of Zeckendorf-selected short golden steps.")),
                    Paragraph(Text(
                        "Reverse-and-negate applies the Hopf antipode to the chronological component while preserving the bidegree. The first parity character is the Liouville value of the prime product. The second is the product of local golden long-short signs.")),
                    Paragraph(Text(
                        "For a word contained in one prime channel, the scalar frequency and terminal Euler phase factor through the bidegree. The Magnus coordinate retains oriented order and changes sign under reversal."))),
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

    private static Formula TimeReversalLawsFormula()
    {
        Formula observe = F.Id("f");
        Formula time = F.Id("t");
        Formula prime = F.Id("p");
        Formula events = F.Id("w");
        Formula negObserve = Seq(Minus, observe);
        Formula reversed = Call("reverse", events);
        Formula bidegree = Call("primeGoldenBidegree", events);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Comma, Sp, Forall, Sp, time, Comma, Sp,
            Forall, Sp, prime, Colon, Sp, F.Id("Nat"), Dot, F.Id("Primes"), Comma, Sp,
            Forall, Sp, events, Comma, RowBreak, Grp(),
            Call("isSinglePrimeWord", prime, events), Sp, Rightarrow, RowBreak, Grp(),
            Call("bigradedChronologicalSignature", negObserve, reversed), Sp, Eq, Sp,
            Call("bigradedAntipode", Call("bigradedChronologicalSignature", observe, events)),
            Sp, Land, RowBreak, Grp(),
            Call("factorParityCharacter", bidegree), Sp, Eq, Sp,
            Call("liouville", Call("primeWordProduct", events)),
            Sp, Land, RowBreak, Grp(),
            Call("goldenStepParityCharacter", bidegree), Sp, Eq, Sp,
            Call("prod", Call("map", F.Id("goldenStepParityLetter"), events)),
            Sp, Land, RowBreak, Grp(),
            Call("scalarStepEndpoint", time, events), Sp, Eq, Sp,
            Call("bidegreePhase", time, prime, bidegree),
            Sp, Land, RowBreak, Grp(),
            Call("doubledMagnusDegreeTwo",
                Call("chronologicalSignature", negObserve, reversed)), Sp, Eq, Sp,
            Minus, Call("doubledMagnusDegreeTwo",
                Call("chronologicalSignature", observe, events)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
