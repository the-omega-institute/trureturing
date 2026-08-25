using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class SelectedObservationInformationMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected finite experiments carry monotone information about a hidden state.",
        H("Selected Observation Information Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("selected-observation-information-monotone"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/"
                        + "SelectedObservationInformationMonotonicity."
                        + "selected_observation_information_monotone"),
                H("Selected observation information is monotone"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the experiment index, hidden state, sample space, and each "
                            + "experiment-output alphabet be finite. A probability mass "
                            + "on samples and the hidden and experiment readouts construct "
                            + "the selected output tuple and its joint law with the hidden "
                            + "state.")),
                    Paragraph(Text(
                        "When S is contained in T, restriction of a T-output tuple to S "
                            + "is deterministic postprocessing. Finite data processing "
                            + "therefore gives F(S) at most F(T), where F is the mutual "
                            + "information of the constructed selected-output joint law. "
                            + "This monotonicity holds without the source section's stronger "
                            + "conditional-independence assumption."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula mass = F.Id("p");
        Formula hidden = F.Id("X");
        Formula outputs = F.Id("Y");
        Formula smaller = F.Id("S");
        Formula larger = F.Id("T");

        Formula probabilityLaw = Call("ProbabilityLaw", mass);
        Formula inclusion = new Formula.Relation(
            smaller, FormulaRelationOperator.SubsetOf, larger);
        Formula informationInequality = new Formula.Relation(
            Call("selectedObservationInformation", mass, hidden, outputs, smaller),
            FormulaRelationOperator.LessThanOrEqual,
            Call("selectedObservationInformation", mass, hidden, outputs, larger));
        Formula assumptions = new Formula.Logic(
            probabilityLaw,
            FormulaLogicOperator.And,
            inclusion);

        return F.Disp(new Formula.Logic(
            assumptions,
            FormulaLogicOperator.Implies,
            informationInequality));
    }
}
