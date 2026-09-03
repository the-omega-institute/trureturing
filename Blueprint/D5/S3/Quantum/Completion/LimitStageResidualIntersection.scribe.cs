using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class LimitStageResidualIntersectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A limit-stage residual is the intersection of all predecessor residuals.",
        H("Limit-Stage Residual Intersection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("limit-stage-residual-is-the-predecessor-intersection"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/LimitStageResidualIntersection."
                        + "limit_stage_residual_intersection"),
                H("Limit-stage residuals are predecessor intersections"),
                StatementSource.FromAuthor(LimitResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a monotone indexed tower of closed subspaces in a complete "
                            + "real-or-complex inner-product space. Define the residual at "
                            + "each stage alpha by R(alpha) = V(alpha)^perp, and fix a stage "
                            + "lambda.")),
                    Paragraph(Text(
                        "The premise identifies the space at lambda with the closed supremum "
                            + "of the spaces at all strictly earlier stages. Equivalently, "
                            + "this supremum is the closed linear span of their union.")),
                    Paragraph(Text(
                        "Orthogonal complementation sends that closed supremum to the "
                            + "intersection of the residuals at every predecessor. "
                            + "The proof directly applies the pinned Mathlib identity "
                            + "ClosedSubmodule.iInf_orthogonal."))),
                DescribeRole.Theorem))));

    private static Formula LimitResidualFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula indexType = F.Id("I");
        Formula tower = F.Id("V");
        Formula residual = F.Id("R");
        Formula stage = F.Id("lambda");
        Formula predecessor = F.Id("alpha");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula closedSubspace = Seq(
            Operatorname, Grp(F.Id("ClosedSubmodule")), Underscore, Grp(scalar),
            Open, space, Close);
        Formula stageSpace = Apply(tower, stage);
        Formula predecessorSpace = Apply(tower, predecessor);
        Formula stageResidual = Apply(residual, stage);
        Formula predecessorResidual = Apply(residual, predecessor);
        Formula predecessorCondition = Seq(predecessor, Lt, stage);
        Formula closedSupremum = Call(
            "ClosedSup", Sub(predecessorSpace, predecessorCondition));
        Formula residualIntersection = Call(
            "Inf", Sub(predecessorResidual, predecessorCondition));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, indexType,
                Colon, Sp, type, Comma),
            Seq(Grp(), Typeclass("RCLike", scalar), Sp, Land, Sp,
                Typeclass("NormedAddCommGroup", space), Sp, Land, Sp,
                Typeclass("InnerProductSpace", scalar, space), Sp, Land),
            Seq(Grp(), Typeclass("CompleteSpace", space), Sp, Land, Sp,
                Typeclass("Preorder", indexType), Comma),
            Seq(Forall, Sp, tower, Comma, Sp, residual, Colon, Sp,
                indexType, Sp, To, Sp,
                closedSubspace, Comma, Sp, stage, Colon, Sp, indexType, Comma),
            Seq(Call("Monotone", tower), Sp, Land, Sp),
            Seq(Open, Forall, Sp, predecessor, Colon, Sp, indexType, Comma, Sp,
                predecessorResidual, Sp, Eq, Sp, Orthogonal(predecessorSpace), Close,
                Sp, Land, Sp),
            Seq(stageSpace, Sp, Eq, Sp, closedSupremum, Sp, Rightarrow),
            Seq(stageResidual, Sp, Eq, Sp, residualIntersection, Dot)
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Orthogonal(Formula subspace) =>
        Seq(subspace, Caret, Grp(Perp));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);
}
