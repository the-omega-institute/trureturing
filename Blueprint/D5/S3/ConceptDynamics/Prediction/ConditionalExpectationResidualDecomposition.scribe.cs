using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class ConditionalExpectationResidualDecompositionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula ambient = F.Id("SigmaX");
        Formula conceptSigma = F.Id("SigmaB");
        Formula measure = F.Id("mu");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula residual = F.Id("R");
        Formula observable = F.Id("Z");
        Formula realNumbers = Seq(Mathbb, Grp(F.Id("R")));
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula l2 = Call("L2", state, measure, realNumbers);
        Formula generatedSigma = Call("comap", concept, conceptSigma);
        Formula generatedSpace = Call(
            "lpMeas", realNumbers, D(2), generatedSigma, ambient, measure);
        Formula estimate = Call(
            "condExpL2", target, generatedSigma, ambient, measure);
        Formula residualIdentity = Seq(
            residual, Sp, Eq, Sp, target, Sp, Minus, Sp, estimate);
        Formula decomposition = Seq(
            target, Sp, Eq, Sp, estimate, Sp, Plus, Sp, residual);
        Formula orthogonality = Seq(
            Forall, Sp, observable, Colon, Sp, generatedSpace, Comma, Sp,
            Call("inner", residual, observable), Sp, Eq, Sp, D(0));

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, conceptType, Colon, Sp, universe,
            Comma, RowBreak, Grp(),
            ambient, Colon, Sp, Call("MeasurableSpace", state), Comma, Sp,
            conceptSigma, Colon, Sp, Call("MeasurableSpace", conceptType),
            Comma, RowBreak, Grp(),
            measure, Colon, Sp, Call("Measure", state), Comma, Sp,
            concept, Colon, Sp, state, Sp, To, Sp, conceptType, Comma,
            RowBreak, Grp(),
            target, Colon, Sp, l2, Comma, Sp,
            Call("Measurable", concept, ambient, conceptSigma),
            RowBreak, Grp(),
            Rightarrow, Sp, Exists, Bang, Sp,
            residual, Colon, Sp, l2, Comma, RowBreak, Grp(),
            residualIdentity, Sp, Land, Sp,
            decomposition, Sp, Land, RowBreak, Grp(),
            orthogonality, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Conditional expectation gives the canonical orthogonal residual "
                + "decomposition over a concept-generated sigma-algebra.",
            H("Conditional Expectation Residual Decomposition"),
            Blocks(Describe.Lean(
                DescribeId.Create(
                    "conditional-expectation-residual-orthogonal-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Prediction/"
                        + "ConditionalExpectationResidualDecomposition."
                        + "conditional_expectation_residual_orthogonal_decomposition"),
                H("Conditional expectation residuals are orthogonal"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ambient and concept-value measurable spaces are explicit. "
                            + "The concept map constructs its generated sigma-algebra by "
                            + "measurable-space comap, and the estimate is Mathlib's real "
                            + "L2 conditional expectation on that subspace.")),
                    Paragraph(Text(
                        "The unique residual is publicly identified as the target minus "
                            + "that estimate, reconstructs the target, and has zero inner "
                            + "product with every square-integrable variable in the same "
                            + "generated measurable subspace."))),
                DescribeRole.Theorem))));
    }
}
