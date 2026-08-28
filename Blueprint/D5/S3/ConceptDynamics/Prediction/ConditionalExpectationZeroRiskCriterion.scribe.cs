using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class ConditionalExpectationZeroRiskCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula measure = F.Id("mu");
        Formula observation = F.Id("q");
        Formula target = F.Id("T");
        Formula generated = Call("comap", observation);
        Formula conditional = Call("condExp", target, generated, measure);
        Formula residual = Seq(target, Sp, Minus, Sp, conditional);
        Formula squaredResidual = new Formula.Power(
            Seq(Grp(residual)), Grp(D(2)));
        Formula risk = Call("Integral", squaredResidual, measure);
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula realNumbers = Seq(Mathbb, Grp(F.Id("R")));

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, universe,
            Comma, RowBreak, Grp(),
            OpenBracket, Call("MeasurableSpace", state), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("MeasurableSpace", output), CloseBracket,
            Comma, RowBreak, Grp(),
            measure, Colon, Sp, Call("Measure", state), Comma, Sp,
            OpenBracket, Call("IsProbabilityMeasure", measure), CloseBracket,
            Comma, RowBreak, Grp(),
            observation, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            Call("Measurable", observation), Comma, RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, realNumbers, Comma, Sp,
            Call("MemLp", target, D(2), measure), RowBreak, Grp(),
            Rightarrow, Sp,
            Open, risk, Sp, Eq, Sp, D(0), Close, Sp, Iff, RowBreak, Grp(),
            Call("AEStronglyMeasurable", target, generated, measure), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Zero conditional squared-error risk exactly characterizes almost-everywhere "
                + "measurability for the observation-generated sigma-algebra.",
            H("Conditional Expectation Zero-Risk Criterion"),
            Blocks(Describe.Lean(
                DescribeId.Create("zero-prediction-risk-iff-ae-observation-measurable"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Prediction/"
                        + "ConditionalExpectationZeroRiskCriterion."
                        + "zero_prediction_risk_iff_ae_observation_measurable"),
                H("Zero prediction risk characterizes observable targets"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The measurable observation map constructs its visible sigma-algebra "
                            + "by measurable-space comap. The displayed conditional expectation "
                            + "is Mathlib's canonical predictor on that sigma-algebra.")),
                    Paragraph(Text(
                        "Square integrability makes the pointwise squared residual integrable. "
                            + "Its nonnegative integral is zero precisely when the residual "
                            + "vanishes almost everywhere. The conditional expectation is "
                            + "measurable on the generated sigma-algebra, and its measurable "
                            + "fixed-point theorem gives the converse."))),
                DescribeRole.Theorem))));
    }
}
