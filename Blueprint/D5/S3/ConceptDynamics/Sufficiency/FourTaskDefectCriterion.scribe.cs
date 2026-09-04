using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class FourTaskDefectCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Sufficiency/FourTaskDefectCriterion."
            + "four_task_defect_zero_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite four-task defect vanishes exactly when all four named tasks descend.",
        H("Four-Task Defect Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-task-defect-zero-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Zero defect is equivalent to four task-relative conditions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The numeric defect is the sum of four finite cardinalities: target "
                        + "disagreements, transported-flow disagreements, admissibility "
                        + "disagreements, and extra states in the anchor fiber.")),
                Paragraph(Text(
                    "A zero sum makes every defect set empty and yields the three descended "
                        + "maps plus a singleton anchor fiber. Conversely, the four conditions "
                        + "exclude every listed defect.")),
                Paragraph(Text(
                    "This is completeness only for the specified target, flow, admissibility "
                        + "predicate, and anchor. It makes no absolute ontological completeness "
                        + "claim."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Compose(Formula function, Formula argument) =>
        Seq(function, Sp, Circ, Sp, argument);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)],
            body);

    private static Formula ForallOne(string name, Formula type, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)],
            body);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("B");
        Formula flowState = F.Id("Y");
        Formula flowCoordinate = F.Id("C");
        Formula targetType = F.Id("Z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula cut = F.Id("q");
        Formula target = F.Id("T");
        Formula targetCut = F.Id("qY");
        Formula flow = F.Id("F");
        Formula admit = F.Id("A");
        Formula anchor = F.Id("a");
        Formula point = F.Id("x");
        Formula descendedTarget = F.Id("Tbar");
        Formula descendedFlow = F.Id("Fbar");
        Formula descendedAdmit = F.Id("Abar");

        Formula targetDescent = ExistsOne(
            "Tbar",
            Arrow(coordinate, targetType),
            Equal(target, Compose(descendedTarget, cut)));
        Formula flowDescent = ExistsOne(
            "Fbar",
            Arrow(coordinate, flowCoordinate),
            Equal(Compose(targetCut, flow), Compose(descendedFlow, cut)));
        Formula admitDescent = ExistsOne(
            "Abar",
            Arrow(coordinate, F.Id("Prop")),
            ForallOne(
                "x",
                state,
                Iff(
                    Apply(admit, point),
                    Apply(descendedAdmit, Apply(cut, point)))));
        Formula anchorFiber = ForallOne(
            "x",
            state,
            Seq(
                Equal(Apply(cut, point), Apply(cut, anchor)),
                Sp, Rightarrow, Sp,
                Equal(point, anchor)));
        Formula tasks = And(
            targetDescent,
            And(flowDescent, And(admitDescent, anchorFiber)));
        Formula defectZero = Equal(
            Apply(
                F.Id("fourTaskDefect"),
                cut,
                target,
                targetCut,
                flow,
                admit,
                anchor),
            new Formula.Number(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, coordinate, Comma, Sp, flowState,
                    Comma, Sp, flowCoordinate, Comma, Sp, targetType),
                type),
            Comma, RowBreak, Grp(),
            Apply(F.Id("Finite"), state),
            Comma, Sp,
            Typed(cut, Arrow(state, coordinate)),
            Comma, Sp,
            Typed(target, Arrow(state, targetType)),
            Comma, RowBreak, Grp(),
            Typed(targetCut, Arrow(flowState, flowCoordinate)),
            Comma, Sp,
            Typed(flow, Arrow(state, flowState)),
            Comma, RowBreak, Grp(),
            Typed(admit, Arrow(state, F.Id("Prop"))),
            Comma, Sp,
            Typed(anchor, state),
            Comma, RowBreak, Grp(),
            Iff(defectZero, tasks), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
