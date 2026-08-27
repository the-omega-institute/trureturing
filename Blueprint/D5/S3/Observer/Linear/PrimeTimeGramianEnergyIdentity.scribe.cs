using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class PrimeTimeGramianEnergyIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity."
            + "prime_time_gramian_energy_identity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted prime-time Gramian quadratic form equals trace-readout energy.",
        H("Prime-Time Gramian Energy Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-time-gramian-energy-identity"),
                DeclarationHandle.Create(Declaration),
                H("The Gramian quadratic form is total weighted trace energy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the canonical real trace-zero Hermitian carrier, form each "
                            + "centered effect by applying the supplied Heisenberg evolution "
                            + "at its time index and then removing its scalar trace part.")),
                    Paragraph(Text(
                        "The prime evidence partition, precision weight, geometric time "
                            + "weight, and context-outcome weight construct a weighted "
                            + "rank-one operator for every five-component index.")),
                    Paragraph(Text(
                        "Whenever this operator family is summable, continuous evaluation "
                            + "and the real inner product transport its sum term by term. "
                            + "Hermitian trace reality then identifies each term with the "
                            + "squared modulus of the corresponding trace readout.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no packaged theorem "
                            + "for the complete five-index identity. Canonical centered-effect, "
                            + "trace-zero carrier, prime-evidence, and rank-one constructions "
                            + "are reused directly."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula Apply(Formula function, params Formula[] arguments) =>
            new Formula.Apply(function, [.. arguments]);
        Formula d = F.Id("d"), context = F.Id("Context"), outcome = F.Id("Outcome");
        Formula s = F.Id("s"), beta = Beta, heisenberg = F.Id("H");
        Formula effects = F.Id("E"), contextWeight = F.Id("w"), difference = F.Id("D");
        Formula p = F.Id("p"), k = F.Id("k"), b = F.Id("b");
        Formula a = F.Id("a"), t = F.Id("t");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula primes = F.Id("NatPrimes");
        Formula hermitian = Call("HermitianSpace", d);
        Formula traceZero = Call("HermitianTraceZero", Call("Fin", d));
        Formula indexType = Seq(
            primes, Sp, Times, Sp, naturals, Sp, Times, Sp, context, Sp, Times, Sp,
            outcome, Sp, Times, Sp, naturals);
        Formula primePartition = F.Id("primePartition");
        Formula precisionWeight = F.Id("precisionWeight");
        Formula timeWeight = F.Id("timeWeight");
        Formula centered = F.Id("centered");
        Formula gramTerm = F.Id("gramTerm");
        Formula gramian = F.Id("gramian");
        Formula evidence = Apply(F.Id("primeEvidence"), s, p);
        Formula partitionSum = Seq(
            Sum, Underscore, Grp(p, InMacro, Sp, primes), Sp,
            Apply(F.Id("primeEvidence"), s, p));
        Formula precisionExponent = Seq(
            Minus, s, Sp, Times, Sp, Open, k, Plus, D(1), Close);
        Formula precision = Seq(
            Open, D(1), Minus, evidence, Close, Sp, Times, Sp,
            p, Caret, Grp(precisionExponent), Sp,
            Slash, Sp, primePartition);
        Formula temporal = Seq(
            Open, D(1), Minus, beta, Close, Sp, Times, Sp, beta, Caret, Grp(t));
        Formula evolvedEffect = Seq(
            Open, heisenberg, Caret, Grp(t), Close,
            Open, Apply(effects, p, k, b, a), Close);
        Formula centeredValue = Apply(F.Id("centeredEffect"), evolvedEffect);
        Formula centeredAt = Apply(centered, p, k, b, a, t);
        Formula scalarWeight = Seq(
            Apply(precisionWeight, p, k), Sp, Times, Sp,
            Apply(timeWeight, t), Sp, Times, Sp,
            Apply(contextWeight, b, a));
        Formula rankOne = Call("rankOne", reals, centeredAt, centeredAt);
        Formula termValue = Seq(scalarWeight, Sp, Times, Sp, rankOne);
        Formula sumBinders = Seq(
            p, InMacro, Sp, primes, Comma, Sp,
            k, InMacro, Sp, naturals, Comma, Sp,
            b, InMacro, Sp, context, Comma, Sp,
            a, InMacro, Sp, outcome, Comma, Sp,
            t, InMacro, Sp, naturals);
        Formula gramianSum = Seq(
            Sum, Underscore, Grp(sumBinders), Sp,
            Apply(gramTerm, p, k, b, a, t));
        Formula inner = Seq(
            Langle, Sp, difference, Comma, Sp, Apply(gramian, difference),
            Sp, Rangle, Underscore, Grp(F.Id("HS")));
        Formula trace = Call("Tr", Seq(
            Call("matrix", difference), Sp, Times, Sp, Call("matrix", centeredAt)));
        Formula energyTerm = Seq(
            scalarWeight, Sp, Times, Sp, new Formula.Norm(trace), Caret, Grp(D(2)));
        Formula energy = Seq(
            Sum, Underscore, Grp(sumBinders), Sp, energyTerm);

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak, Grp(),
            context, Comma, Sp, outcome, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            s, Comma, Sp, beta, InMacro, Sp, reals, Comma, RowBreak, Grp(),
            heisenberg, Colon, Sp, Call("LinearMap", reals, hermitian, hermitian), Comma,
            RowBreak, Grp(),
            effects, Colon, Sp, indexType, Sp, To, Sp, hermitian, Comma,
            RowBreak, Grp(),
            contextWeight, Colon, Sp, context, Sp, Times, Sp, outcome,
            Sp, To, Sp, reals, Comma,
            RowBreak, Grp(),
            difference, InMacro, Sp, traceZero, Comma, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            primePartition, Sp, Colon, Eq, Sp, partitionSum, Semi,
            RowBreak, Grp(),
            precisionWeight, Open, p, Comma, Sp, k, Close, Sp, Colon, Eq, Sp,
            precision, Semi, RowBreak, Grp(),
            timeWeight, Open, t, Close, Sp, Colon, Eq, Sp, temporal, Semi,
            RowBreak, Grp(),
            centered, Open, p, Comma, Sp, k, Comma, Sp, b, Comma, Sp, a,
            Comma, Sp, t, Close, Sp, Colon, Eq, Sp, centeredValue, Semi,
            RowBreak, Grp(),
            gramTerm, Open, p, Comma, Sp, k, Comma, Sp, b, Comma, Sp, a,
            Comma, Sp, t, Close, Sp, Colon, Eq, Sp, termValue, Semi,
            RowBreak, Grp(),
            Apply(F.Id("Summable"), gramTerm), Sp, Rightarrow, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            gramian, Sp, Colon, Eq, Sp, gramianSum, Semi, RowBreak, Grp(),
            inner, Sp, Eq, Sp, energy, Dot));
    }

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
}
