using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class IdentityRestorationValueCompensationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Restoration/IdentityRestorationValueCompensation."
            + "identity_restoration_implies_value_compensation_and_converse_countermodel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity restoration preserves identity-determined value, while equal-value "
            + "compensation need not restore identity.",
        H("Identity Restoration and Value Compensation"),
        Blocks(Describe.Lean(
            DescribeId.Create("identity-restoration-value-compensation"),
            DeclarationHandle.Create(Declaration),
            H("Restoration implies compensation but not conversely"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The forward clause applies the frozen restoration theorem directly: "
                        + "a factor from identity values to functional values transports the "
                        + "restored-identity equality to value compensation.")),
                Paragraph(Text(
                    "The converse clause uses one shared two-state construction. Identity is "
                        + "the Bool identity readout, value is constant Unit, harm swaps the "
                        + "states, and repair is the identity process. The common value is "
                        + "preserved although the state identity is not restored."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula identityCarrier = Sub(F.Id("B"), F.Id("I"));
        Formula valueCarrier = Sub(F.Id("B"), F.Id("V"));
        Formula identity = F.Id("I");
        Formula value = F.Id("V");
        Formula harm = F.Id("U");
        Formula repair = F.Id("R");
        Formula x = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula repaired = Apply(repair, Apply(harm, x));
        Formula identityRestored = Seq(
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(identity, repaired), Sp, Eq, Sp, Apply(identity, x));
        Formula valueRestored = Seq(
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(value, repaired), Sp, Eq, Sp, Apply(value, x));
        Formula forward = Seq(
            Forall, Sp, state, Comma, Sp, identityCarrier, Comma, Sp, valueCarrier,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            identity, Colon, Sp, state, Sp, To, Sp, identityCarrier, Comma, Sp,
            value, Colon, Sp, state, Sp, To, Sp, valueCarrier, Comma, RowBreak, Grp(),
            harm, Comma, Sp, repair, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            Call("Refines", value, identity), Sp, Land, Sp,
            Open, identityRestored, Close,
            Sp, Rightarrow, Sp, Open, valueRestored, Close);

        Formula counterIdentity = Sub(identity, F.Id("c"));
        Formula counterValue = Sub(value, F.Id("c"));
        Formula counterHarm = Sub(harm, F.Id("c"));
        Formula counterRepair = Sub(repair, F.Id("c"));
        Formula boolType = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula counterState = F.Id("b");
        Formula identityMap = Seq(
            Open, counterState, Sp, Mapsto, Sp, counterState, Close);
        Formula constantUnitMap = Seq(
            Open, counterState, Sp, Mapsto, Sp, Star, Close);
        Formula complementMap = Seq(
            Open, counterState, Sp, Mapsto, Sp, Neg, Sp, counterState, Close);
        Formula counterRepaired = Apply(counterRepair, Apply(counterHarm, counterState));
        Formula counterValueRestored = Seq(
            Forall, Sp, counterState, Colon, Sp, boolType, Comma, Sp,
            Apply(counterValue, counterRepaired), Sp, Eq, Sp,
            Apply(counterValue, counterState));
        Formula counterIdentityRestored = Seq(
            Forall, Sp, counterState, Colon, Sp, boolType, Comma, Sp,
            Apply(counterIdentity, counterRepaired), Sp, Eq, Sp,
            Apply(counterIdentity, counterState));
        Formula countermodel = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Define(counterIdentity, Seq(boolType, Sp, To, Sp, boolType), identityMap),
            Comma, Sp,
            Define(counterValue, Seq(boolType, Sp, To, Sp, unit),
                constantUnitMap), Comma, Sp,
            Define(counterHarm, Seq(boolType, Sp, To, Sp, boolType), complementMap),
            Comma, Sp,
            Define(counterRepair, Seq(boolType, Sp, To, Sp, boolType), identityMap),
            Comma, Sp,
            Operatorname, Grp(F.Id("in")), Sp,
            Open, Call("Refines", counterValue, counterIdentity), Sp, Land, Sp,
            Open, counterValueRestored, Close, Sp, Land, Sp, Neg, Sp,
            Open, counterIdentityRestored, Close, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, forward, Close, Sp, Land,
            RowBreak, Grp(), Open, countermodel, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Define(Formula name, Formula type, Formula value) =>
        Seq(Typed(name, type), Sp, Colon, Eq, Sp, value);
}
