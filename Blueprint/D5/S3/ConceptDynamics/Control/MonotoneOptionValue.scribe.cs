using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class MonotoneOptionValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A monotone future-value function preserves inclusion between post-action feasible futures.",
        H("Monotone Option Value"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monotone-option-value"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Control/MonotoneOptionValue.monotone_option_value"),
                H("More feasible futures cannot have lower monotone value"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An action acts on the current state through F. Feasibility R then "
                            + "constructs the future-option set at the resulting state.")),
                    Paragraph(Text(
                        "The public premises state that W is monotone on future sets and that "
                            + "every future feasible after v is also feasible after u.")),
                    Paragraph(Text(
                        "Applying monotonicity to that inclusion gives the displayed value "
                            + "order. The option sets remain explicit constructions from the "
                            + "transition and feasibility primitives."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula FeasibleSet(
        Formula future,
        Formula futureType,
        Formula feasible,
        Formula step,
        Formula action,
        Formula state) =>
        Seq(
            OpenBrace, future, Colon, Sp, futureType, Sp, Mid, Sp,
            Apply(feasible, Apply(step, action, state), future), CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("U");
        Formula futureType = F.Id("Z");
        Formula valueType = F.Id("L");
        Formula step = F.Id("F");
        Formula feasible = F.Id("R");
        Formula value = F.Id("W");
        Formula preferred = F.Id("u");
        Formula dominated = F.Id("v");
        Formula state = F.Id("x");
        Formula future = F.Id("z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula futureSet = Call("Set", futureType);
        Formula dominatedOptions =
            FeasibleSet(future, futureType, feasible, step, dominated, state);
        Formula preferredOptions =
            FeasibleSet(future, futureType, feasible, step, preferred, state);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, actionType, Comma, Sp,
            futureType, Comma, Sp, valueType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("Preorder", valueType), Comma, Sp,
            step, Colon, Sp, Arrow(actionType, Arrow(stateType, stateType)), Comma,
            RowBreak, Grp(),
            feasible, Colon, Sp, Arrow(stateType, Arrow(futureType, proposition)), Comma, Sp,
            value, Colon, Sp, Arrow(futureSet, valueType), Comma,
            RowBreak, Grp(),
            Call("Monotone", value), Comma, Sp,
            preferred, Comma, Sp, dominated, Colon, Sp, actionType, Comma, Sp,
            state, Colon, Sp, stateType, Comma,
            RowBreak, Grp(),
            dominatedOptions, Sp, Subseteq, Sp, preferredOptions,
            Sp, Rightarrow, RowBreak, Grp(),
            Apply(value, dominatedOptions), Sp, Leq, Sp,
            Apply(value, preferredOptions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
