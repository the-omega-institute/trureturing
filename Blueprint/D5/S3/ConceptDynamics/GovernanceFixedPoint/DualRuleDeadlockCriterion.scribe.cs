using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class DualRuleDeadlockCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A repair class is deadlocked exactly when it has no jointly allowed repair.",
        H("Dual-Rule Deadlock Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("deadlocked-iff-empty-joint-allowance"),
            DeclarationHandle.Create(Prefix + "deadlocked_iff_empty_joint_allowance"),
            H("Deadlock is empty joint allowance"),
            StatementSource.FromAuthor(DeadlockFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The frozen reachability predicate asks for a repair in both the repair "
                    + "class and the two rules' joint allowance. Negating that witness is "
                    + "equivalent to emptiness of the same intersection."))),
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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula DeadlockFormula()
    {
        Formula repairType = F.Id("Repair");
        Formula repairClass = F.Id("repairClass");
        Formula allowFirst = Seq(F.Id("allow"), Underscore, Grp(D(1)));
        Formula allowSecond = Seq(F.Id("allow"), Underscore, Grp(D(2)));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula setType = Apply(F.Id("Set"), repairType);
        Formula jointAllowed = Apply(F.Id("JointAllowed"), allowFirst, allowSecond);
        Formula intersection = Call("intersection", repairClass, jointAllowed);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(repairType, type), Comma),
            Seq(
                Forall, Sp,
                Typed(
                    Seq(repairClass, Comma, Sp, allowFirst, Comma, Sp, allowSecond),
                    setType),
                Comma, RowBreak, Grp()),
            Seq(
                Apply(F.Id("Deadlocked"), repairClass, allowFirst, allowSecond),
                Sp, Leftrightarrow, Sp),
            Seq(intersection, Sp, Eq, Sp, Emptyset, Dot),
        ]));
    }
}
