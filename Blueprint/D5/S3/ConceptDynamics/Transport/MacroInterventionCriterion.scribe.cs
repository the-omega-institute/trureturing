using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class MacroInterventionCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Macro interventions are characterized by empty carry.",
        H("Macro-Intervention Carry Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("macro-intervention-carry-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/MacroInterventionCriterion."
                        + "macro_intervention_carry_criterion"),
                H("Existence excludes carry; empty carry gives unique descent"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a process, let C be its current readout, and let D be "
                            + "the future readout. A macro intervention G on the ambient "
                            + "readout codomain commutes when G(C(x)) equals D(F(x)) for "
                            + "every source state x.")),
                    Paragraph(Text(
                        "If such an ambient intervention exists, two states identified by C "
                            + "cannot be separated by D after F, so the intervention-carry "
                            + "type is empty. Conversely, in the finite decidable model, "
                            + "empty carry determines a unique intervention on the effective "
                            + "image range(C). The reverse implication directly reuses the "
                            + "repository theorem FiniteReverseCriterion.")),
                    Paragraph(Text(
                        "The two directions deliberately have different domains: the forward "
                            + "hypothesis supplies G on the full readout codomain, while the "
                            + "reverse conclusion asserts uniqueness only on the realized "
                            + "effective image. No extension outside that image is claimed.")),
                    Paragraph(Text(
                        "This formalizes theorem/510.1 of formal-concept-dynamics, atom "
                            + "generic-residual-11d26e8120ab721779698193df66228d9ce5276b1c732"
                            + "982aaeee841a3f83ee2."))),
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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("X");
        Formula processState = F.Id("Y");
        Formula currentType = new Formula.Subscript(F.Id("B"), F.Id("C"));
        Formula futureType = new Formula.Subscript(F.Id("B"), F.Id("D"));
        Formula process = F.Id("F");
        Formula current = F.Id("C");
        Formula future = F.Id("D");
        Formula intervention = F.Id("G");
        Formula effectiveIntervention = Seq(Overline, Grp(intervention));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carry = Apply(
            Seq(Operatorname, Grp(F.Id("Carry"))), process, current, future);
        Formula macroIntervention = Apply(
            Seq(Operatorname, Grp(F.Id("MacroIntervention"))),
            process, current, future, intervention);
        Formula effectiveDescent = Apply(
            Seq(Operatorname, Grp(F.Id("EffectiveImageDescent"))),
            process, current, future, effectiveIntervention);
        Formula range = Apply(
            Seq(Operatorname, Grp(F.Id("range"))), current);
        Formula emptyCarry = Apply(
            Seq(Operatorname, Grp(F.Id("IsEmpty"))), carry);
        Formula forward = Grp(
            Open,
            Open,
            Exists, Sp, intervention, Colon, Sp, Arrow(currentType, futureType), Comma, Sp,
            macroIntervention,
            Close, Sp, Rightarrow, Sp, emptyCarry,
            Close);
        Formula reverse = Grp(
            Open,
            emptyCarry, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, effectiveIntervention, Colon, Sp,
            Arrow(range, futureType), Comma, Sp, effectiveDescent,
            Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, processState, Comma, Sp,
            currentType, Comma, Sp, futureType, Colon, Sp, type, Comma, Esc,
            Typeclass("Fintype", state), Comma, Sp,
            Typeclass("DecidableEq", state), Comma, Sp,
            Typeclass("Fintype", currentType), Comma, Sp,
            Typeclass("DecidableEq", currentType), Comma, Sp,
            Typeclass("Fintype", futureType), Comma, Sp,
            Typeclass("DecidableEq", futureType), Comma, Esc,
            process, Colon, Sp, Arrow(state, processState), Comma, Sp,
            current, Colon, Sp, Arrow(state, currentType), Comma, Sp,
            future, Colon, Sp, Arrow(processState, futureType), Comma, Esc,
            forward, Sp, Land, Sp, reverse, Dot));
    }
}
