using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class StabilizerSelectorObstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction."
            + "no_equivariant_selector_of_stabilizer_without_fixed_action";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stabilizer without an admissible fixed action obstructs every equivariant selector.",
        H("Stabilizer Obstruction to Equivariant Selection"),
        Blocks(Describe.Lean(
            DescribeId.Create("stabilizer-without-fixed-action-obstructs-equivariant-selector"),
            DeclarationHandle.Create(Declaration),
            H("No equivariant selector exists without a stabilizer-fixed action"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a group act on both states and actions. At the named state, every "
                        + "admissible action is moved by some group element that fixes the state; "
                        + "this states directly that the stabilizer has no admissible fixed action.")),
                Paragraph(Text(
                    "An admissible deterministic selector would choose one of those actions. "
                        + "Equivariance under the corresponding stabilizer element would both "
                        + "fix and move the selected action, a contradiction.")),
                Paragraph(Text(
                    "The existing finite-permutation culprit theorem is only a specialization. "
                        + "Repository and pinned-Mathlib searches found no general group-action "
                        + "theorem with the public admissible-set and stabilizer clauses."))),
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
        Formula movesEveryAction = Seq(
            Forall, Sp, action, Colon, Sp, actionType, Comma, Sp,
            action, Sp, InMacro, Sp, Apply(admissible, state), Sp,
            Rightarrow, Sp,
            Exists, Sp, symmetry, Colon, Sp, group, Comma, Sp,
            Call("smul", symmetry, state), Sp, Eq, Sp, state, Sp, Land, Sp,
            Call("smul", symmetry, action), Sp, Neq, Sp, action);
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
            admissible, Colon, Sp, admissibleType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            Open, movesEveryAction, Close, Sp, Rightarrow, Sp,
            Neg, Sp, Exists, Sp, selector, Colon, Sp,
            Arrow(stateType, actionType), Comma, RowBreak, Grp(),
            Open, selectsAdmissibly, Close, Sp, Land, Sp,
            Open, equivariant, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
