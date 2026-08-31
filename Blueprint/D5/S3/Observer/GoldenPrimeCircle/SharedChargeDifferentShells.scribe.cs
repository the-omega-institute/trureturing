using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class SharedChargeDifferentShellsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct observer shells may factor through the same charge readout while retaining different residual information.",
        H("Shared Charge, Different Shells"),
        Blocks(
            Theorem("common-charge-agreement", "common_charge_agreement",
                "Common Charge Projections Agree", CommonChargeAgreementFormula(),
                "If two shell maps both factor the same charge observation, their projected readings agree at every source point.",
                "The equality is only after applying the respective charge projections; it does not identify the shell outputs themselves."),
            Theorem("concrete-shells-carry-same-charge", "concrete_shells_carry_same_charge",
                "The Concrete Shells Carry the Same Charge", ConcreteShellsCarrySameChargeFormula(),
                "The coarse Boolean shell reads the first coordinate, while the fine shell retains the full pair and projects its first coordinate as charge.",
                "Both factorizations recover the same source charge, but the conjunction alone does not assert equal information content."),
            Theorem("same-charge-different-observer-witness", "same_charge_different_observer_witness",
                "One Coarse Collision Is Separated by the Fine Shell", SameChargeDifferentObserverWitnessFormula(),
                "The inputs (true,false) and (true,true) have the same coarse first-coordinate reading.",
                "Their fine-shell values remain distinct, giving a concrete residual distinction beyond the shared charge."),
            Theorem("shared-charge-does-not-force-same-resolution", "shared_charge_does_not_force_same_resolution",
                "Shared Charge Does Not Force Equal Resolution", SharedChargeDoesNotForceSameResolutionFormula(),
                "There exist two Boolean-pair inputs that collide under the coarse shell and are separated by the fine shell.",
                "This existential counterexample refutes only equality of observer resolution from shared charge; it does not compare arbitrary shell orders."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula CommonChargeAgreementFormula()
    {
        Formula xType = F.Id("X"); Formula yOne = Subscript(F.Id("Y"), D(1));
        Formula yTwo = Subscript(F.Id("Y"), D(2)); Formula chargeType = F.Id("C");
        Formula shellOne = Subscript(F.Id("shell"), D(1));
        Formula shellTwo = Subscript(F.Id("shell"), D(2));
        Formula chargeOne = Subscript(F.Id("charge"), D(1));
        Formula chargeTwo = Subscript(F.Id("charge"), D(2));
        Formula charge = F.Id("charge"); Formula x = F.Id("x");
        return Statement(
            [Typed(xType, Universe(F.Id("u"))), Typed(yOne, Universe(F.Id("v"))),
                Typed(yTwo, Universe(F.Id("w"))), Typed(chargeType, Universe(F.Id("z"))),
                Typed(shellOne, Arrow(xType, yOne)), Typed(shellTwo, Arrow(xType, yTwo)),
                Typed(chargeOne, Arrow(yOne, chargeType)), Typed(chargeTwo, Arrow(yTwo, chargeType)),
                Typed(charge, Arrow(xType, chargeType)), Typed(x, xType)],
            [Call("CarriesCharge", shellOne, chargeOne, charge),
                Call("CarriesCharge", shellTwo, chargeTwo, charge)],
            Seq(Apply(chargeOne, Apply(shellOne, x)), Sp, Eq, Sp,
                Apply(chargeTwo, Apply(shellTwo, x))));
    }

    private static Formula ConcreteShellsCarrySameChargeFormula()
    {
        Formula first = F.Id("fst");
        return Statement([], [], Conjunction(
            Call("CarriesCharge", F.Id("coarseShell"), F.Id("id"), first),
            Call("CarriesCharge", F.Id("fineShell"), F.Id("fineCharge"), first)));
    }

    private static Formula SameChargeDifferentObserverWitnessFormula()
    {
        Formula left = Pair(F.Id("true"), F.Id("false"));
        Formula right = Pair(F.Id("true"), F.Id("true"));
        return Statement([], [], Conjunction(
            Seq(Call("coarseShell", left), Sp, Eq, Sp, Call("coarseShell", right)),
            Seq(Call("fineShell", left), Sp, Neq, Sp, Call("fineShell", right))));
    }

    private static Formula SharedChargeDoesNotForceSameResolutionFormula()
    {
        Formula x = F.Id("x"); Formula y = F.Id("y"); Formula pairType = BoolPair();
        Formula witness = Conjunction(
            Seq(Call("coarseShell", x), Sp, Eq, Sp, Call("coarseShell", y)),
            Seq(Call("fineShell", x), Sp, Neq, Sp, Call("fineShell", y)));
        return Statement([], [], Seq(
            Exists, Sp, Typed(x, pairType), Comma, Sp, Typed(y, pairType), Comma, Sp,
            Open, witness, Close));
    }

    private static Formula Statement(Formula[] binders, Formula[] hypotheses, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp); AddSeparated(items, binders, Comma);
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        if (hypotheses.Length > 0)
        {
            AddSeparated(items, hypotheses.Select(h => Seq(Open, h, Close)).ToArray(), Land);
            items.Add(Sp); items.Add(Rightarrow); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static void AddSeparated(List<Formula> items, Formula[] values, Formula separator)
    {
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) { items.Add(Sp); items.Add(separator); items.Add(Sp); }
            items.Add(values[index]);
        }
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Universe(Formula level) => Seq(Operatorname, Grp(F.Id("Type")), Underscore, Grp(level));
    private static Formula Subscript(Formula value, Formula subscript) => Seq(value, Underscore, Grp(subscript));
    private static Formula Apply(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Pair(Formula first, Formula second) => Seq(Open, first, Comma, Sp, second, Close);
    private static Formula BoolPair() => Seq(Operatorname, Grp(F.Id("Bool")), Sp, Times, Sp, Operatorname, Grp(F.Id("Bool")));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);
}
