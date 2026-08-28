using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transportability;

internal sealed class MacroInterventionCarryCharacterizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Transportability/MacroInterventionCarryCharacterization."
            + "macro_intervention_carry_characterization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intervention carry characterizes effective-image macro descent.",
        H("Macro-Intervention Carry Characterization"),
        Blocks(Describe.Lean(
            DescribeId.Create("macro-intervention-carry-characterization"),
            DeclarationHandle.Create(Declaration),
            H("Carry emptiness and macro-intervention existence constrain each other"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be a micro-level intervention on X and let C map micro states "
                        + "to the macro carrier Z. The imported family primitives define "
                        + "ambient commutation, intervention carry, and descent on range(C).")),
                Paragraph(Text(
                    "The forward clause needs only an ambient commuting intervention. The "
                        + "reverse clause independently needs only empty carry and constructs "
                        + "a unique map on the realized image, without a finiteness premise.")),
                Paragraph(Text(
                    "The final public clause takes an actual carry inhabitant and rules out "
                        + "every ambient commuting intervention, exposing the source theorem's "
                        + "nonexistence-witness interpretation directly."))),
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula macroState = F.Id("Z");
        Formula intervention = F.Id("F");
        Formula concept = F.Id("C");
        Formula ambient = F.Id("G");
        Formula effective = F.Id("Gbar");
        Formula carryWitness = F.Id("kappa");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carry = Call("Carry", intervention, concept, concept);
        Formula ambientLaw = Call(
            "MacroIntervention", intervention, concept, concept, ambient);
        Formula effectiveLaw = Call(
            "EffectiveImageDescent", intervention, concept, concept, effective);
        Formula emptyCarry = Call("IsEmpty", carry);
        Formula ambientExists = Seq(
            Exists, Sp, ambient, Colon, Sp, Arrow(macroState, macroState), Comma, Sp,
            ambientLaw);
        Formula forward = Seq(
            Open, ambientExists, Close, Sp, Rightarrow, Sp, emptyCarry);
        Formula reverse = Seq(
            emptyCarry, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, effective, Colon, Sp,
            Arrow(Call("range", concept), macroState), Comma, Sp, effectiveLaw);
        Formula witness = Seq(
            Forall, Sp, carryWitness, Colon, Sp, carry, Comma, Sp,
            Neg, Open, ambientExists, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, macroState, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            intervention, Colon, Sp, Arrow(state, state), Comma, Sp,
            concept, Colon, Sp, Arrow(state, macroState), Comma,
            RowBreak, Grp(),
            Open, forward, Close, Sp, Land, RowBreak, Grp(),
            Open, reverse, Close, Sp, Land, RowBreak, Grp(),
            Open, witness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
