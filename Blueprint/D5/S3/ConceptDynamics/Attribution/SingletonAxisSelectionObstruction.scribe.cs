using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class SingletonAxisSelectionObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Attribution/SingletonAxisSelectionObstruction."
            + "no_equivariant_singleton_axis_selector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A globally fixed state cannot equivariantly select an axis when no axis is globally fixed.",
        H("Singleton Axis Selection Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("globally-fixed-state-has-no-equivariant-axis-selector"),
            DeclarationHandle.Create(Declaration),
            H("No canonical axis can be selected from a completely symmetric state"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a group act on states and axes. The named state is fixed by every "
                        + "group element, so its singleton is an invariant subaction.")),
                Paragraph(Text(
                    "If every axis is moved by some group element, an equivariant selector "
                        + "from that singleton would force its selected axis to be globally "
                        + "fixed, a contradiction.")),
                Paragraph(Text(
                    "The proof instantiates the frozen stabilizer-selector obstruction on the "
                        + "constructed singleton subaction. Repository and pinned-library "
                        + "searches found no theorem with this exact singleton domain."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula stateType = F.Id("X");
        Formula axisType = F.Id("A");
        Formula omega = Omega;
        Formula symmetry = F.Id("g");
        Formula axis = F.Id("a");
        Formula state = F.Id("x");
        Formula selector = F.Id("sigma");
        Formula fixedSingleton = F.Id("XOmega");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula fixedState = Seq(
            Forall, Sp, Typed(symmetry, group), Comma, Sp,
            Call("smul", symmetry, omega), Sp, Eq, Sp, omega);
        Formula noFixedAxis = Seq(
            Forall, Sp, Typed(axis, axisType), Comma, Sp,
            Exists, Sp, Typed(symmetry, group), Comma, Sp,
            Call("smul", symmetry, axis), Sp, Neq, Sp, axis);
        Formula singletonConstruction = Seq(
            Open, OpenBrace, omega, CloseBrace, Comma, Sp,
            Open, fixedState, Close, Close);
        Formula equivariant = Seq(
            Forall, Sp, Typed(symmetry, group), Comma, Sp,
            Typed(state, fixedSingleton), Comma, Sp,
            Call("apply", selector, Call("smul", symmetry, state)), Sp,
            Eq, Sp, Call("smul", symmetry, Call("apply", selector, state)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                Typed(Seq(group, Comma, Sp, stateType, Comma, Sp, axisType), type), Comma),
            Seq(Grp(), Typeclass("Group", group), Comma, Sp,
                Typeclass("MulAction", group, stateType), Comma, Sp,
                Typeclass("MulAction", group, axisType), Comma),
            Seq(Grp(), Forall, Sp, Typed(omega, stateType), Comma),
            Seq(Grp(), Open, fixedState, Close, Sp, Land, Sp,
                Open, noFixedAxis, Close, Sp, Rightarrow),
            Seq(Grp(), F.Id("let"), Sp,
                Typed(fixedSingleton, Call("SubMulAction", group, stateType)), Sp,
                Eq, Sp, singletonConstruction, Semi),
            Seq(Grp(), Neg, Sp, Exists, Sp,
                Typed(selector, Arrow(fixedSingleton, axisType)), Comma, Sp,
                Open, equivariant, Close, Dot),
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
