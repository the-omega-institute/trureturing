using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class SelectedObservationInformationMonotonicityCanonicalDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected canonical joint readouts carry monotone mutual information.",
        H("Selected Observation Information Monotonicity, Canonical Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("selected-observation-information-monotone-canonical"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/"
                        + "SelectedObservationInformationMonotonicityCanonical."
                        + "selected_observation_information_monotone_canonical"),
                H("Selected canonical readout information is monotone"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the experiment index, hidden state, sample space, and each "
                            + "experiment-output alphabet be finite. A probability mass on "
                            + "samples and the hidden and experiment readouts construct each "
                            + "selected tuple through the canonical joint readout.")),
                    Paragraph(Text(
                        "When S is contained in T, restricting a T-output tuple to S is "
                            + "deterministic postprocessing, so finite data processing gives "
                            + "the displayed inequality. Conditional independence is not "
                            + "needed for this monotonicity clause."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([F.Comma, F.Sp]);
            items.Add(arguments[index]);
        }
        items.Add(F.Close);
        return F.Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        F.Seq(value, F.Colon, F.Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, F.Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([F.Comma, F.Sp]);
            items.Add(arguments[index]);
        }
        items.Add(F.Close);
        return F.Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Seq(F.Operatorname, F.Grp(F.Id("Type")));
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula sampleType = F.Id("Sample");
        Formula hiddenType = F.Id("Hidden");
        Formula indexType = F.Id("Index");
        Formula outputFamily = F.Id("Output");
        Formula mass = F.Id("mass");
        Formula hidden = F.Id("hidden");
        Formula output = F.Id("output");
        Formula smaller = F.Id("S");
        Formula larger = F.Id("T");
        Formula index = F.Id("i");
        Formula sample = F.Id("s");
        Formula selectedIndex = F.Id("j");
        Formula outputAtIndex = Apply(outputFamily, index);
        Formula outputType = F.Seq(
            F.Forall, F.Sp, Typed(index, indexType), F.Comma, F.Sp,
            Arrow(sampleType, outputAtIndex));
        Formula selectedOutput(Formula selected) => F.Seq(
            selectedIndex, F.Colon, F.Sp, selected, F.Sp, F.Mapsto, F.Sp,
            Apply(output, Call("val", selectedIndex)));
        Formula smallerReadout = Call(
            "jointReadout", selectedOutput(smaller));
        Formula largerReadout = Call(
            "jointReadout", selectedOutput(larger));
        Formula smallerLaw = Call("readoutTargetLaw", mass, smallerReadout, hidden);
        Formula largerLaw = Call("readoutTargetLaw", mass, largerReadout, hidden);
        Formula finiteOutputs = F.Seq(
            F.Forall, F.Sp, Typed(index, indexType), F.Comma, F.Sp,
            Call("Fintype", outputAtIndex));
        Formula massLaw = F.Seq(
            OpenLaw(
                F.Forall, F.Sp, Typed(sample, sampleType), F.Comma, F.Sp,
                F.D(0), F.Sp, F.Leq, F.Sp, Apply(mass, sample)),
            F.Sp, F.Land, F.Sp,
            F.Sum, F.Underscore, F.Grp(Typed(sample, sampleType)), F.Sp,
            Apply(mass, sample), F.Sp, F.Eq, F.Sp, F.D(1));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, Typed(sampleType, type), F.Comma, F.Sp,
            Typed(hiddenType, type), F.Comma, F.Sp, Typed(indexType, type), F.Comma,
            F.RowBreak, F.Grp(),
            Typed(outputFamily, Arrow(indexType, type)), F.Comma, F.RowBreak, F.Grp(),
            OpenLaw(
                Call("Fintype", sampleType), F.Sp, F.Land, F.Sp,
                Call("Fintype", hiddenType), F.Sp, F.Land, F.Sp, finiteOutputs),
            F.Sp, F.Rightarrow, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, Typed(mass, Arrow(sampleType, real)), F.Comma, F.Sp,
            Typed(hidden, Arrow(sampleType, hiddenType)), F.Comma, F.RowBreak, F.Grp(),
            Typed(output, outputType), F.Comma, F.RowBreak, F.Grp(),
            Typed(smaller, Call("Finset", indexType)), F.Comma, F.Sp,
            Typed(larger, Call("Finset", indexType)), F.Comma, F.RowBreak, F.Grp(),
            OpenLaw(massLaw), F.Sp, F.Land, F.Sp,
            smaller, F.Sp, F.Subseteq, F.Sp, larger, F.Sp, F.Rightarrow,
            F.RowBreak, F.Grp(),
            Call("mutualInformation", smallerLaw), F.Sp, F.Leq, F.Sp,
            Call("mutualInformation", largerLaw), F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    private static Formula OpenLaw(params Formula[] items) =>
        F.Seq(F.Open, F.Seq(items), F.Close);
}
