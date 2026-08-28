using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class EquivalentLawPosteriorInteriorDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivalent transcript laws keep the limiting binary posterior strictly interior and "
            + "exclude measurable zero-error separation.",
        H("Posterior Interiority under Equivalent Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equivalent-law-posterior-stays-interior"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior."
                        + "equivalent_law_posterior_stays_interior"),
                H("Equivalent laws keep the limiting posterior interior"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two state-indexed transcript laws are probability measures on one "
                            + "measurable space. A real prior strictly between zero and one "
                            + "constructs their displayed mixture law.")),
                    Paragraph(Text(
                        "The limiting likelihood is the real Radon--Nikodym density of the first "
                            + "law with respect to the second. Mutual absolute continuity makes "
                            + "this density finite and positive almost everywhere under the "
                            + "mixture, so the displayed Bayesian normalization is strictly "
                            + "between zero and one.")),
                    Paragraph(Text(
                        "The second conjunct applies the frozen null-set transport result: no "
                            + "measurable event can have mass one under the first law and mass "
                            + "zero under the equivalent second law."))),
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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula transcript = F.Id("Omega");
        Formula outcome = F.Id("omega");
        Formula prior = F.Id("a");
        Formula probabilityX = Seq(F.Id("P"), Underscore, Grp(F.Id("x")));
        Formula probabilityY = Seq(F.Id("P"), Underscore, Grp(F.Id("y")));
        Formula eventSet = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula measure = Call("Measure", transcript);
        Formula likelihood = Call(
            "toReal", Call("rnDeriv", probabilityX, probabilityY, outcome));
        Formula weightedLikelihood = Seq(prior, Sp, likelihood);
        Formula complement = Seq(Open, D(1), Sp, Minus, Sp, prior, Close);
        Formula posterior = Seq(
            Frac, Grp(weightedLikelihood),
            Grp(weightedLikelihood, Sp, Plus, Sp, complement));
        Formula mixedLaw = Seq(
            Call("ofReal", prior), Sp, probabilityX, Sp, Plus, Sp,
            Call("ofReal", Seq(D(1), Sp, Minus, Sp, prior)), Sp, probabilityY);
        Formula equivalent = Seq(
            Call("AbsolutelyContinuous", probabilityX, probabilityY), Sp, Land, Sp,
            Call("AbsolutelyContinuous", probabilityY, probabilityX));
        Formula interior = Call(
            "AlmostEverywhere", mixedLaw,
            Seq(outcome, Sp, Mapsto, Sp,
                D(0), Sp, Lt, Sp, posterior, Sp, Land, Sp,
                posterior, Sp, Lt, Sp, D(1)));
        Formula separator = Seq(
            Call("Measurable", eventSet), Sp, Land, Sp,
            Apply(probabilityX, eventSet), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Apply(probabilityY, eventSet), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, transcript, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("MeasurableSpace", transcript), CloseBracket,
            Comma, RowBreak, Grp(),
            probabilityX, Comma, Sp, probabilityY, Colon, Sp, measure,
            Comma, Sp, prior, Colon, Sp, reals, Comma, RowBreak, Grp(),
            Call("ProbabilityMeasure", probabilityX), Sp, Land, Sp,
            Call("ProbabilityMeasure", probabilityY), Sp, Land, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, prior, Sp, Land, Sp,
            prior, Sp, Lt, Sp, D(1), Sp, Land, Sp, equivalent,
            RowBreak, Grp(), Rightarrow, Sp,
            interior, Sp, Land, RowBreak, Grp(),
            Neg, Exists, Sp, eventSet, Colon, Sp, Call("Set", transcript),
            Comma, Sp, separator, Dot));
    }
}
