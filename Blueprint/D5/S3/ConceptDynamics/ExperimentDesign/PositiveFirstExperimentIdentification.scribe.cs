using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class PositiveFirstExperimentIdentificationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification."
            + "positive_first_experiment_identifies_model";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive first experiment identifies the forward causal model.",
        H("Positive First-Experiment Identification"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-first-experiment-identifies-model"),
            DeclarationHandle.Create(Declaration),
            H("A positive first result identifies the model"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The first experiment is the canonical Boolean readout on the three-model "
                    + "carrier. By construction it is positive exactly on the model in which "
                    + "changing X changes the law of Y."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("m");
        Formula firstExperiment = new Formula.Subscript(F.Id("E"), F.Id("X"));
        Formula forwardModel = new Formula.Subscript(F.Id("M"), F.Id("XY"));

        return Disp(Seq(
            Forall, Sp, model, Colon, Sp, Call("Fin", D(3)), Comma, Sp,
            firstExperiment, Open, model, Close, Sp, Eq, Sp, F.Id("true"),
            Sp, Rightarrow, Sp, model, Sp, Eq, Sp, forwardModel, Dot));
    }
}
