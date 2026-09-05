using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenBidegreeFrequencyRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenBidegreeFrequencyRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In one prime channel, irrational golden frequency faithfully recovers the prime-event and short-step counts.",
        H("Prime-Golden Bidegree Frequency Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-bidegree-frequency-rigidity"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_bidegree_frequency_rigidity"),
                H("Real frequency recovers the bidegree count ledger"),
                StatementSource.FromAuthor(FrequencyRigidityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For fixed prime p, the scalar frequency of bidegree (k,s) is (k phi^2 - s) log p.")),
                    Paragraph(Text(
                        "The nonzero prime logarithm and irrationality of the golden ratio make this map injective on natural-number bidegrees.")),
                    Paragraph(Text(
                        "The result recovers event count and short-step count, while chronology within the recovered bidegree remains outside the scalar frequency readout."))),
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

    private static Formula FrequencyRigidityFormula()
    {
        Formula prime = F.Id("p");
        Formula left = F.Id("u");
        Formula right = F.Id("w");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Colon, Sp, F.Id("Nat"), Dot, F.Id("Primes"), Comma, RowBreak, Grp(),
            Call("Injective", Call("bidegreeFrequency", prime)),
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, left, Comma, Sp, right, Comma, Sp,
            Call("isSinglePrimeWord", prime, left), Sp, Rightarrow, Sp,
            Call("isSinglePrimeWord", prime, right), Sp, Rightarrow, RowBreak, Grp(),
            Call("totalStepFrequency", left), Sp, Eq, Sp, Call("totalStepFrequency", right),
            Sp, Rightarrow, Sp,
            Call("primeGoldenBidegree", left), Sp, Eq, Sp, Call("primeGoldenBidegree", right), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
