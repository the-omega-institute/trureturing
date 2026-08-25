using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class SmallPrimeChannelOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first m primes maximize information among m complete equal-cost channels.",
        H("Small Prime Channel Optimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-prime-channel-optimality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ArithmeticTomography/SmallPrimeChannelOptimality."
                        + "small_prime_channel_optimality"),
                H("The first m prime channels maximize total information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The parameter s is publicly restricted to the open interval above one. "
                            + "The function H assigns expected information to every complete "
                            + "prime channel at each such parameter, and the displayed premise "
                            + "states its strict decrease as the prime grows.")),
                    Paragraph(Text(
                        "An order embedding c from Fin(m) into the natural numbers represents "
                            + "an increasing choice of exactly m distinct channels. The public "
                            + "primality premise ensures that every selected index is a prime; "
                            + "the shared cardinality is the equal-cost budget constraint.")),
                    Paragraph(Text(
                        "The canonical increasing enumeration of the prime subtype is pointwise "
                            + "no larger than any such ordered choice. Strict decrease of H turns "
                            + "that comparison around, and summing the pointwise inequalities "
                            + "proves the displayed maximum."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula parameter = F.Id("s");
        Formula information = F.Id("H");
        Formula channelCount = F.Id("m");
        Formula chosen = F.Id("c");
        Formula prime = F.Id("p");
        Formula largerPrime = F.Id("r");
        Formula index = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula primes = Seq(Operatorname, Grp(F.Id("Primes")));
        Formula finiteIndex = Call("Fin", channelCount);
        Formula informationType = Seq(
            Call("Ioi", D(1)), Sp, To, Sp, primes, Sp, To, Sp, reals);
        Formula chosenType = Call("OrderEmbedding", finiteIndex, naturals);
        Formula InformationAt(Formula p) => Apply(information, parameter, p);
        Formula ChosenAt(Formula i) => Apply(chosen, i);
        Formula PrimeAt(Formula i) => Call("prime", i);
        Formula selectedSum = Seq(
            Sum, Underscore, Grp(index, InMacro, Sp, finiteIndex), Sp,
            InformationAt(ChosenAt(index)));
        Formula firstPrimeSum = Seq(
            Sum, Underscore, Grp(index, InMacro, Sp, finiteIndex), Sp,
            InformationAt(PrimeAt(index)));
        Formula strictlyDecreasing = Seq(
            Forall, Sp, prime, Comma, Sp, largerPrime, Sp, InMacro, Sp, primes,
            Comma, Sp, prime, Sp, Lt, Sp, largerPrime, Sp, Rightarrow, Sp,
            InformationAt(largerPrime), Sp, Lt, Sp, InformationAt(prime));
        Formula selectedArePrime = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, finiteIndex, Comma, Sp,
            Call("Prime", ChosenAt(index)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, parameter, Sp, InMacro, Sp, reals, Comma, Sp,
            information, Colon, Sp, informationType, Comma, RowBreak, Grp(),
            channelCount, Sp, InMacro, Sp, naturals, Comma, Sp,
            chosen, Colon, Sp, chosenType, Comma, RowBreak, Grp(),
            D(1), Sp, Lt, Sp, parameter, Sp, Land, Sp,
            Open, strictlyDecreasing, Close, Sp, Land, Sp,
            Open, selectedArePrime, Close, Sp, Rightarrow, RowBreak, Grp(),
            selectedSum, Sp, Leq, Sp, firstPrimeSum, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
