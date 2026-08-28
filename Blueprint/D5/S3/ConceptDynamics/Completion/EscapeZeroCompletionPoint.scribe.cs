using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class EscapeZeroCompletionPointDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Completion/EscapeZeroCompletionPoint."
            + "escape_zero_iff_determined_with_audited_minimizer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful escape zero is equivalent to determination by the joined readout, and a "
            + "unique audited parameter supplies the regularized completion point.",
        H("Escape-Zero Completion Point"),
        Blocks(Describe.Lean(
            DescribeId.Create("escape-zero-iff-determined-with-audited-minimizer"),
            DeclarationHandle.Create(Declaration),
            H("Escape zero characterizes the audited completion point"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A baseline readout q is joined with the parameter-dependent definition "
                        + "readout d(a). The escape defect is the supplied weight of target "
                        + "pairs that the joint readout still identifies.")),
                Paragraph(Text(
                    "Faithfulness says that a set has zero weight exactly when it is empty. "
                        + "The repository's sufficiency-escape equivalence then gives both "
                        + "directions between zero defect and target factorization through "
                        + "the joined readout.")),
                Paragraph(Text(
                    "An audited parameter has exactly three properties: it globally minimizes "
                        + "Delta(a) + lambda Cost(d(a)), its joint readout determines the target, "
                        + "and its escape defect is zero. Under the source's unique-existence "
                        + "condition, the selected witness kappa has each property and every "
                        + "other audited parameter equals it."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula DeltaAt(
        Formula baseline,
        Formula definitions,
        Formula target,
        Formula weight,
        Formula parameter) =>
        Call("parameterEscapeDefect", baseline, definitions, target, weight, parameter);

    private static Formula Objective(
        Formula baseline,
        Formula definitions,
        Formula target,
        Formula weight,
        Formula cost,
        Formula lambda) =>
        Call(
            "regularizedCompletionObjective",
            baseline,
            definitions,
            target,
            weight,
            cost,
            lambda);

    private static Formula Audit(
        Formula baseline,
        Formula definitions,
        Formula target,
        Formula weight,
        Formula cost,
        Formula lambda,
        Formula parameter) =>
        Call(
            "IsAuditedCompletionParameter",
            baseline,
            definitions,
            target,
            weight,
            cost,
            lambda,
            parameter);

    private static Formula Determines(
        Formula baseline,
        Formula definitions,
        Formula target,
        Formula parameter) =>
        Call(
            "FactorsThrough",
            target,
            Call("conceptJoin", baseline, Apply(definitions, parameter)));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula parameterType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula baselineType = F.Id("Q");
        Formula targetType = F.Id("Y");
        Formula definitionType = F.Id("D");
        Formula baseline = F.Id("q");
        Formula definitions = F.Id("d");
        Formula target = F.Id("T");
        Formula weight = F.Id("w");
        Formula cost = F.Id("Cost");
        Formula lambda = LambdaLower;
        Formula parameter = F.Id("a");
        Formula set = F.Id("S");
        Formula candidate = F.Id("candidate");
        Formula unique = F.Id("uniqueCompletion");
        Formula kappa = Call("choose", unique);
        Formula statePair = Call("Prod", stateType, stateType);
        Formula objective = Objective(
            baseline, definitions, target, weight, cost, lambda);

        Formula faithful = Seq(
            Forall, Sp, Typed(set, Call("Set", statePair)), Comma, Sp,
            Call("mass", weight, set), Sp, Eq, Sp, D(0), Sp,
            Leftrightarrow, Sp, set, Sp, Eq, Sp, Emptyset);
        Formula uniqueAudit = Seq(
            Exists, Bang, Sp, Typed(Kappa, parameterType), Comma, Sp,
            Audit(baseline, definitions, target, weight, cost, lambda, Kappa));

        Formula conclusions = Seq(
            Begin, Grp(F.Id("gathered")),
            Open,
            DeltaAt(baseline, definitions, target, weight, parameter),
            Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Determines(baseline, definitions, target, parameter),
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Determines(baseline, definitions, target, parameter),
            Sp, Rightarrow, Sp,
            DeltaAt(baseline, definitions, target, weight, parameter),
            Sp, Eq, Sp, D(0),
            Close, Sp, Land, RowBreak, Grp(),
            Call("IsMinOn", objective, Call("SetUniv", parameterType), kappa),
            Sp, Land, RowBreak, Grp(),
            DeltaAt(baseline, definitions, target, weight, kappa),
            Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Determines(baseline, definitions, target, kappa),
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(candidate, parameterType), Comma, Sp,
            Audit(baseline, definitions, target, weight, cost, lambda, candidate),
            Sp, Rightarrow, Sp, candidate, Sp, Eq, Sp, kappa,
            End, Grp(F.Id("gathered")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(parameterType, Comma, Sp, stateType, Comma, Sp,
                    baselineType, Comma, Sp, targetType),
                type),
            Comma, RowBreak, Grp(),
            Typed(definitionType, Arrow(parameterType, type)), Comma, RowBreak, Grp(),
            Typed(baseline, Arrow(stateType, baselineType)), Comma, Sp,
            Typed(
                definitions,
                Seq(Forall, Sp, Typed(parameter, parameterType), Comma, Sp,
                    Arrow(stateType, Apply(definitionType, parameter)))),
            Comma, RowBreak, Grp(),
            Typed(target, Arrow(stateType, targetType)), Comma, Sp,
            Typed(weight, Call("EscapeWeight", statePair)), Comma, RowBreak, Grp(),
            Typed(
                cost,
                Seq(Forall, Sp, Typed(parameter, parameterType), Comma, Sp,
                    Arrow(
                        Arrow(stateType, Apply(definitionType, parameter)),
                        real))),
            Comma, Sp, Typed(lambda, real), Comma, Sp,
            Typed(parameter, parameterType), Comma, RowBreak, Grp(),
            Open, faithful, Close, Sp, Rightarrow, Sp,
            Open, Typed(unique, uniqueAudit), Close, Sp, Rightarrow, RowBreak, Grp(),
            conclusions,
            End, Grp(F.Id("gathered"))));
    }
}
