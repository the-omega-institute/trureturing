using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class ConditionalExpectationOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula measure = F.Id("mu");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula predictor = F.Id("h");
        Formula composedPredictor = Seq(predictor, Sp, Circ, Sp, concept);
        Formula conditional = Call(
            "condExpL2", target, Call("comap", concept));
        Formula leftError = Seq(target, Sp, Minus, Sp, conditional);
        Formula rightError = Seq(target, Sp, Minus, Sp, composedPredictor);
        Formula leftMeanSquare = new Formula.Power(
            Call("L2Norm", leftError, measure), Grp(D(2)));
        Formula rightMeanSquare = new Formula.Power(
            Call("L2Norm", rightError, measure), Grp(D(2)));
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, conceptType, Colon, Sp, universe,
            Comma, RowBreak, Grp(),
            measure, Colon, Sp, Call("Measure", state), Comma, Sp,
            concept, Colon, Sp, state, Sp, To, Sp, conceptType, Comma,
            RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp,
            predictor, Colon, Sp, conceptType, Sp, To, Sp,
            Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            Call("Measurable", concept), Sp, Land, Sp,
            Call("MemLp", target, D(2), measure), Sp, Land,
            RowBreak, Grp(),
            Call("Measurable", predictor), Sp, Land, Sp,
            Call("MemLp", composedPredictor, D(2), measure),
            RowBreak, Grp(),
            Rightarrow, Sp,
            leftMeanSquare, Sp, Leq, Sp, rightMeanSquare, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Conditional expectation is the best squared-error predictor measurable "
                + "through a concept.",
            H("Conditional Expectation Optimality"),
            Blocks(Describe.Lean(
                DescribeId.Create("conditional-expectation-minimizes-mean-square-error"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality."
                        + "conditional_expectation_minimizes_mean_square_error"),
                H("Conditional expectation minimizes mean-square error"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concept map generates a sub-sigma-algebra by measurable-space comap. "
                        + "Every square-integrable measurable function of the concept belongs "
                        + "to the corresponding measurable subspace of the ambient real L2 "
                        + "space. Conditional expectation is its orthogonal projection, whose "
                        + "minimal-distance property gives the displayed squared-error bound."))),
                DescribeRole.Theorem))));
    }
}
