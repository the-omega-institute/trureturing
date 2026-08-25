using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FunctionalGraphs;

internal sealed class FinitenessIsNotImmediateDegeneracyDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationRoot =
        "D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dynamics eventually cycle without forcing short periods, short transients, "
            + "or rich readouts.",
        H("Finiteness Is Not Immediate Degeneracy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("periodic-structure-readout-richness"),
                DeclarationHandle.Create(
                    DeclarationRoot
                        + "periodic_structure_does_not_determine_readout_richness"),
                H("Periodic structure does not determine readout richness"),
                StatementSource.FromAuthor(ReadoutRichnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source leaves semantic quality undefined. The formal fallback "
                            + "measures only the number of readout values realized on the "
                            + "periodic core and introduces no quality axiom.")),
                    Paragraph(Text(
                        "Two Boolean identity systems have equivalent periodic cores and equal "
                            + "minimal periods. A constant readout realizes one value, while the "
                            + "identity readout realizes both Boolean values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiteness-necessary"),
                DeclarationHandle.Create(DeclarationRoot + "finiteness_is_necessary"),
                H("Finiteness is necessary"),
                StatementSource.FromAuthor(FinitenessNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The successor map on the concrete infinite carrier Nat has no "
                            + "periodic orbit point, so its orbit from zero never enters a "
                            + "periodic core."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiteness-not-immediate-degeneracy"),
                DeclarationHandle.Create(
                    DeclarationRoot + "finiteness_is_not_immediate_degeneracy"),
                H("Finiteness is not immediate degeneracy"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every self-map of a finite carrier eventually enters the canonical "
                            + "periodic core. This clause directly reuses the repository's finite "
                            + "orbit periodicity theorem.")),
                    Paragraph(Text(
                        "Cyclic ZMod translations give arbitrarily large exact minimal periods. "
                            + "Finite countdown maps give arbitrarily large exact transient "
                            + "lengths before reaching their unique periodic state.")),
                    Paragraph(Text(
                        "For every fixed window, a sufficiently long cyclic translation has "
                            + "pairwise distinct states throughout that window despite already "
                            + "being periodic.")),
                    Paragraph(Text(
                        "The Lean module separately checks empty and singleton carriers, constant "
                            + "and identity maps, exact transient length zero, and a zero-length "
                            + "initial window."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ReadoutRichnessFormula()
    {
        Formula boolean = Seq(Mathbb, Grp(F.Id("B")));
        Formula endomorphism = new Formula.TypeArrow(boolean, boolean);
        Formula tauLow = F.Id("tauLow"), tauHigh = F.Id("tauHigh");
        Formula qLow = F.Id("qLow"), qHigh = F.Id("qHigh");
        Formula falseValue = F.Id("false");
        Formula lowCore = Apply(F.Id("PeriodicCore"), tauLow);
        Formula highCore = Apply(F.Id("PeriodicCore"), tauHigh);
        Formula lowValues = Apply(F.Id("periodicReadoutValues"), tauLow, qLow);
        Formula highValues = Apply(F.Id("periodicReadoutValues"), tauHigh, qHigh);

        return Disp(Seq(
            Exists, Sp, Typed(tauLow, endomorphism), Comma, Sp,
            Typed(tauHigh, endomorphism), Comma, RowBreak,
            Typed(qLow, endomorphism), Comma, Sp, Typed(qHigh, endomorphism), Comma, RowBreak,
            Apply(F.Id("Nonempty"), Seq(lowCore, Sp, Equiv, Sp, highCore)), Sp, Land, RowBreak,
            Apply(F.Id("minimalPeriod"), tauLow, falseValue), Sp, Eq, Sp,
            Apply(F.Id("minimalPeriod"), tauHigh, falseValue), Sp, Land, RowBreak,
            Card(lowValues), Sp, Lt, Sp, Card(highValues), Dot));
    }

    private static Formula FinitenessNecessaryFormula() => Disp(Seq(
        Neg, Sp, Apply(F.Id("EventuallyEntersPeriodicCore"), F.Id("succ"), D(0)), Dot));

    private static Formula MainFormula()
    {
        Formula carrier = F.Id("Y"), update = Tau, initial = F.Id("y");
        Formula threshold = F.Id("N"), length = F.Id("ell");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finite = Apply(F.Id("Finite"), carrier);
        Formula fintype = Apply(F.Id("Fintype"), carrier);
        Formula enters = Apply(F.Id("EventuallyEntersPeriodicCore"), update, initial);
        Formula minimalPeriod = Apply(F.Id("minimalPeriod"), update, initial);
        Formula transient = Apply(F.Id("HasTransientLength"), update, initial, length);
        Formula injective = Apply(F.Id("InitialOrbitInjective"), update, initial, threshold);

        return Disp(Seq(
            Open, Forall, Sp, carrier, Comma, Sp, finite, Sp, Rightarrow, Sp,
                Forall, Sp, update, Comma, Sp, initial, Comma, Sp, enters, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, threshold, Sp, InMacro, Sp, naturals, Comma, Sp,
                Exists, Sp, carrier, Comma, Sp, update, Comma, Sp, initial, Comma, Sp,
                fintype, Sp, Land, Sp, threshold, Sp, Lt, Sp, minimalPeriod, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, threshold, Sp, InMacro, Sp, naturals, Comma, Sp,
                Exists, Sp, carrier, Comma, Sp, update, Comma, Sp, initial, Comma, Sp,
                length, Comma, Sp, fintype, Sp, Land, Sp,
                threshold, Sp, Lt, Sp, length, Sp, Land, Sp, transient, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, threshold, Sp, InMacro, Sp, naturals, Comma, Sp,
                Exists, Sp, carrier, Comma, Sp, update, Comma, Sp, initial, Comma, Sp,
                fintype, Sp, Land, Sp, injective, Sp, Land, Sp, enters, Close, Dot));
    }
}
