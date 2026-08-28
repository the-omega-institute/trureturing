using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class RestorationCompensationAsymmetryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Restoration/RestorationCompensationAsymmetry."
            + "identity_restoration_implies_compensation_with_converse_countermodel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity restoration implies value compensation, but compensation need not restore identity.",
        H("Restoration and Compensation Asymmetry"),
        Blocks(Describe.Lean(
            DescribeId.Create("identity-restoration-implies-compensation-with-converse-countermodel"),
            DeclarationHandle.Create(Declaration),
            H("Restoration implies compensation and the converse fails"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The forward clause uses the canonical refinement relation to express "
                        + "that identity determines value.")),
                Paragraph(Text(
                    "The converse countermodel uses the same Boolean harm and repair in both "
                        + "halves: negation changes identity, while the constant unit-valued "
                        + "concept remains compensated.")),
                Paragraph(Text(
                    "All countermodel functions and their carriers are displayed explicitly."))),
            DescribeRole.Theorem))));

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

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula identityCarrier = F.Id("IdentityValue");
        Formula valueCarrier = F.Id("FunctionalValue");
        Formula identity = F.Id("I");
        Formula value = F.Id("V");
        Formula harm = F.Id("U");
        Formula repair = F.Id("R");
        Formula point = F.Id("x");
        Formula repaired = At(repair, At(harm, point));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula forward = Seq(
            Open, Forall, Sp, point, Comma, Sp,
            At(identity, repaired), Sp, Eq, Sp, At(identity, point), Close,
            Sp, Rightarrow, Sp,
            Open, Forall, Sp, point, Comma, Sp,
            At(value, repaired), Sp, Eq, Sp, At(value, point), Close);

        Formula counterIdentity = F.Id("I0");
        Formula counterValue = F.Id("V0");
        Formula counterHarm = F.Id("U0");
        Formula counterRepair = F.Id("R0");
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula counterPoint = F.Id("b");
        Formula counterRepaired = At(counterRepair, At(counterHarm, counterPoint));
        Formula valueCompensated = Seq(
            Forall, Sp, counterPoint, Colon, Sp, boolean, Comma, Sp,
            At(counterValue, counterRepaired), Sp, Eq, Sp, At(counterValue, counterPoint));
        Formula identityRestored = Seq(
            Forall, Sp, counterPoint, Colon, Sp, boolean, Comma, Sp,
            At(counterIdentity, counterRepaired), Sp, Eq, Sp,
            At(counterIdentity, counterPoint));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, identityCarrier, Comma, Sp, valueCarrier,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            identity, Colon, Sp, Arrow(state, identityCarrier), Comma, Sp,
            value, Colon, Sp, Arrow(state, valueCarrier), Comma, RowBreak, Grp(),
            harm, Comma, Sp, repair, Colon, Sp, Arrow(state, state), Comma,
            RowBreak, Grp(),
            Call("Refines", value, identity), Comma, RowBreak, Grp(),
            forward, Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            counterIdentity, Colon, Sp, Arrow(boolean, boolean), Sp, Colon, Eq, Sp,
            F.Id("id"), Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            counterValue, Colon, Sp, Arrow(boolean, unit), Sp, Colon, Eq, Sp,
            Open, counterPoint, Sp, Mapsto, Sp, F.Id("unit"), Close,
            Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            counterHarm, Colon, Sp, Arrow(boolean, boolean), Sp, Colon, Eq, Sp,
            Operatorname, Grp(F.Id("BoolNot")), Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            counterRepair, Colon, Sp, Arrow(boolean, boolean), Sp, Colon, Eq, Sp,
            F.Id("id"), Comma, RowBreak, Grp(),
            Call("Refines", counterValue, counterIdentity), Sp, Land, RowBreak, Grp(),
            valueCompensated, Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open, identityRestored, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
