using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FixedSymmetrySelectorObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction."
            + "no_equivariant_selector_of_common_fixed_symmetry";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed-state symmetry without admissible fixed actions obstructs equivariant selection.",
        H("Fixed-Symmetry Obstruction to Equivariant Selection"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-fixed-symmetry-obstructs-equivariant-selector"),
            DeclarationHandle.Create(Declaration),
            H("No equivariant deterministic selector exists under a fixed-point-free stabilizer"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A single group element and state are quantified together. The element "
                        + "fixes that state but moves every action in its admissible set.")),
                Paragraph(Text(
                    "Any everywhere-admissible equivariant selector would choose an action in "
                        + "that set. Equivariance at the fixed state would force the chosen action "
                        + "to be fixed by the same element, contradicting the public premise."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula admissible = F.Id("admissible");
        Formula state = F.Id("x");
        Formula action = F.Id("a");
        Formula symmetry = F.Id("g");
        Formula selector = F.Id("s");
        Formula point = F.Id("y");
        Formula admissibleType = Arrow(stateType, Call("Set", actionType));
        Formula selected = Apply(selector, point);
        Formula commonObstruction = Seq(
            Exists, Sp, state, Colon, Sp, stateType, Comma, Sp,
            symmetry, Colon, Sp, group, Comma, Sp,
            Call("smul", symmetry, state), Sp, Eq, Sp, state, Sp, Land, Sp,
            Open, Forall, Sp, action, Colon, Sp, actionType, Comma, Sp,
            action, Sp, InMacro, Sp, Apply(admissible, state), Sp,
            Rightarrow, Sp,
            Call("smul", symmetry, action), Sp, Neq, Sp, action, Close);
        Formula selectsAdmissibly = Seq(
            Forall, Sp, point, Colon, Sp, stateType, Comma, Sp,
            selected, Sp, InMacro, Sp, Apply(admissible, point));
        Formula equivariant = Seq(
            Forall, Sp, symmetry, Colon, Sp, group, Comma, Sp,
            point, Colon, Sp, stateType, Comma, Sp,
            Apply(selector, Call("smul", symmetry, point)), Sp, Eq, Sp,
            Call("smul", symmetry, selected));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, stateType, Comma, Sp, actionType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("Group", group), CloseBracket, Comma, Sp,
            OpenBracket, Call("MulAction", group, stateType), CloseBracket, Comma, Sp,
            OpenBracket, Call("MulAction", group, actionType), CloseBracket, Comma,
            RowBreak, Grp(),
            admissible, Colon, Sp, admissibleType, Comma, RowBreak, Grp(),
            Open, commonObstruction, Close, Sp, Rightarrow, Sp,
            Neg, Sp, Exists, Sp, selector, Colon, Sp,
            Arrow(stateType, actionType), Comma, RowBreak, Grp(),
            Open, selectsAdmissibly, Close, Sp, Land, Sp,
            Open, equivariant, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
