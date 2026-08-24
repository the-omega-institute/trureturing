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

    private static Formula TheoremFormula()
    {
        Formula mass = F.Id("p");
        Formula hidden = F.Id("X");
        Formula outputs = F.Id("Y");
        Formula smaller = F.Id("S");
        Formula larger = F.Id("T");
        Formula smallerReadout = Call(
            "jointReadout", F.Seq(outputs, F.Sp, F.Mid, F.Sp, smaller));
        Formula largerReadout = Call(
            "jointReadout", F.Seq(outputs, F.Sp, F.Mid, F.Sp, larger));
        Formula smallerLaw = Call("readoutTargetLaw", mass, smallerReadout, hidden);
        Formula largerLaw = Call("readoutTargetLaw", mass, largerReadout, hidden);
        Formula assumptions = new Formula.Logic(
            Call("ProbabilityLaw", mass),
            FormulaLogicOperator.And,
            new Formula.Relation(smaller, FormulaRelationOperator.SubsetOf, larger));
        Formula conclusion = new Formula.Relation(
            Call("mutualInformation", smallerLaw),
            FormulaRelationOperator.LessThanOrEqual,
            Call("mutualInformation", largerLaw));

        return F.Disp(new Formula.Logic(
            assumptions,
            FormulaLogicOperator.Implies,
            conclusion));
    }
}
