using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class CounterfactualRepairSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A successful counterfactual state does not universally imply an admissible allowed repair.",
        H("Counterfactual Repair Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("counterfactual-success-not-imply-allowed-repair"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Control/CounterfactualRepairSeparation."
                        + "counterfactual_success_not_imply_allowed_repair"),
                H("Counterfactual success does not imply allowed repair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "State, action, and result carriers are quantified explicitly. A target, "
                            + "actual state, desired result, allowed-action set, transition, "
                            + "and admissibility predicate are the source primitives.")),
                    Paragraph(Text(
                        "The first public clause is existence of a counterfactual state with the "
                            + "desired target value. The second requires an allowed action whose "
                            + "actual transition reaches that value and is admissible.")),
                    Paragraph(Text(
                        "The theorem negates the universal implication. Its Boolean witness uses "
                            + "the same target, actual state, transition family, and desired value "
                            + "on both sides; the desired state is produced only by an excluded "
                            + "action.")),
                    Paragraph(Text(
                        "No repository theorem states this general non-implication. The proof is "
                            + "an explicit shared-transition countermodel with no new target-shaped "
                            + "definition."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula action = F.Id("U");
        Formula result = F.Id("Y");
        Formula target = F.Id("J");
        Formula actual = F.Id("x");
        Formula desired = F.Id("y");
        Formula allowed = F.Id("A");
        Formula step = F.Id("F");
        Formula admissible = F.Id("Adm");
        Formula stateArrowResult = Seq(state, Sp, To, Sp, result);
        Formula stateArrowState = Seq(action, Sp, To, Sp, state, Sp, To, Sp, state);
        Formula admissibleType = Seq(state, Sp, To, Sp, Operatorname, Grp(F.Id("Prop")));
        Formula counterfactual = Seq(
            Exists, Sp, F.Id("xPrime"), Colon, Sp, state, Comma, Sp,
            Apply(target, F.Id("xPrime")), Sp, Eq, Sp, desired);
        Formula repair = Seq(
            Exists, Sp, F.Id("u"), Colon, Sp, action, Comma, Sp,
            F.Id("u"), Sp, InMacro, Sp, allowed, Sp, Land, Sp,
            Apply(target, Apply(step, F.Id("u"), actual)), Sp, Eq, Sp, desired,
            Sp, Land, Sp, Apply(admissible, Apply(step, F.Id("u"), actual)));
        Formula binders = Seq(
            state, Comma, Sp, action, Comma, Sp, result, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            target, Colon, Sp, stateArrowResult, Comma, Sp,
            actual, Colon, Sp, state, Comma, Sp,
            desired, Colon, Sp, result, Comma, Sp,
            allowed, Colon, Sp, Call("Set", action), Comma, Sp,
            step, Colon, Sp, stateArrowState, Comma, Sp,
            admissible, Colon, Sp, admissibleType);
        return Disp(Seq(
            Neg, Sp, Forall, Sp, binders, Comma, RowBreak, Grp(),
            counterfactual, Sp, Rightarrow, RowBreak, Grp(),
            repair, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
