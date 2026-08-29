using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class ObserverWorldCovarianceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Naturality/ObserverWorldCovariance."
            + "observer_world_covariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Covariant observers on transitive axes have equivalent output worlds.",
        H("Observer World Covariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("covariant-observers-have-equivalent-output-worlds"),
            DeclarationHandle.Create(Declaration),
            H("Any two observer worlds are equivalent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An observer world is constructed directly as the range of that axis's "
                        + "state-to-output map. Transitivity supplies a group element carrying "
                        + "one axis to the other.")),
                Paragraph(Text(
                    "Covariance shows that the corresponding output equivalence maps the first "
                        + "range onto the second. Restricting it to these ranges produces the "
                        + "displayed equivalence and transition computation rule.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found no complete observer-world "
                        + "result. The generic transitivity witness and subtype restriction "
                        + "construction are applied directly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula axisType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula observer = F.Id("O");
        Formula transport = F.Id("U");
        Formula symmetry = F.Id("g");
        Formula axis = F.Id("a");
        Formula targetAxis = F.Id("b");
        Formula state = F.Id("x");
        Formula transition = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula observerType = Arrow(axisType, Arrow(stateType, outputType));
        Formula transportType = Arrow(group, Call("Equiv", outputType, outputType));
        Formula observed = Call("apply", observer, axis, state);
        Formula transformedObserved = Call(
            "apply", observer,
            Call("smul", symmetry, axis),
            Call("smul", symmetry, state));
        Formula transported = Call("apply", transport, symmetry, observed);
        Formula covariance = Seq(
            Forall, Sp, Typed(symmetry, group), Comma, Sp,
            Typed(axis, axisType), Comma, Sp, Typed(state, stateType), Comma, Sp,
            transformedObserved, Sp, Eq, Sp, transported);
        Formula worldA = Call("range", Call("apply", observer, axis));
        Formula worldB = Call("range", Call("apply", observer, targetAxis));
        Formula transitionRule = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Call("apply", transition, observed), Sp, Eq, Sp,
            Call("apply", transport, symmetry, observed));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                Typed(Seq(group, Comma, Sp, axisType, Comma, Sp,
                    stateType, Comma, Sp, outputType), type), Comma),
            Seq(Grp(), Typeclass("Group", group), Comma, Sp,
                Typeclass("MulAction", group, axisType), Comma, Sp,
                Typeclass("MulAction", group, stateType), Comma),
            Seq(Grp(), Typeclass("IsPretransitive", group, axisType), Comma),
            Seq(Grp(), Forall, Sp, Typed(observer, observerType), Comma, Sp,
                Typed(transport, transportType), Comma),
            Seq(Grp(), Open, covariance, Close, Sp, Rightarrow),
            Seq(Grp(), Forall, Sp, Typed(axis, axisType), Comma, Sp,
                Typed(targetAxis, axisType), Comma),
            Seq(Grp(), Exists, Sp, Typed(symmetry, group), Comma, Sp,
                Exists, Sp, Typed(transition, Call("Equiv", worldA, worldB)), Comma),
            Seq(Grp(), Call("smul", symmetry, axis), Sp, Eq, Sp, targetAxis,
                Sp, Land, Sp, Open, transitionRule, Close, Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
