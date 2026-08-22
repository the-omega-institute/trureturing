using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class HeterogeneousFiberMisclassificationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A message fiber with two target values forces a deterministic error.",
        H("Heterogeneous Fiber Misclassification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heterogeneous-fiber-forces-misclassification"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "heterogeneous_fiber_forces_misclassification"),
                H("A heterogeneous message fiber forces an error"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The message and target are arbitrary readouts on one state carrier. "
                            + "Two named states witness heterogeneity by sharing a message while "
                            + "having different target values.")),
                    Paragraph(Text(
                        "Every deterministic inference rule is represented by a function from "
                            + "messages to target values. The public conclusion says directly "
                            + "that its inferred value is wrong at the first witness or at the "
                            + "second witness.")),
                    Paragraph(Text(
                        "Equal messages force equal inferred values. If both inferences were "
                            + "correct, equality transport would contradict the displayed target "
                            + "inequality."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula messageType = F.Id("M");
        Formula targetType = F.Id("Y");
        Formula message = new Formula.Subscript(F.Id("M"), F.Id("S"));
        Formula target = F.Id("T");
        Formula inference = F.Id("delta");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula messageX = Apply(message, x);
        Formula messageY = Apply(message, y);
        Formula targetX = Apply(target, x);
        Formula targetY = Apply(target, y);
        Formula inferenceX = Apply(inference, messageX);
        Formula inferenceY = Apply(inference, messageY);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, messageType, Comma, Sp, targetType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            message, Colon, Sp, stateType, Sp, To, Sp, messageType, Comma, Sp,
            target, Colon, Sp, stateType, Sp, To, Sp, targetType, Comma, RowBreak, Grp(),
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            Open, messageX, Sp, Eq, Sp, messageY, Sp, Land, Sp,
            targetX, Sp, Neq, Sp, targetY, Close, Sp, Rightarrow, Sp, RowBreak, Grp(),
            Forall, Sp, inference, Colon, Sp, messageType, Sp, To, Sp, targetType,
            Comma, Sp, Open,
            inferenceX, Sp, Neq, Sp, targetX, Sp, Lor, Sp,
            inferenceY, Sp, Neq, Sp, targetY, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
