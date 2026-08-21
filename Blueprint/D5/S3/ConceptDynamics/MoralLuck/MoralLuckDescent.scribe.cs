using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.MoralLuck;

internal sealed class MoralLuckDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Control descent is equivalent to the absence of a fiber defect.",
        H("Control Descent and Fiber Defects"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moral-luck-descent"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent.moral_luck_descent_iff"),
                H("Control descent iff no moral-luck witness"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite inhabited state type X, a control readout C, and an "
                            + "evaluation J, the control principle is the existence of a "
                            + "factor map from control values to evaluation values.")),
                    Paragraph(Text(
                        "A witness is a pair of states with equal control values and unequal "
                            + "evaluations. The repository's answerability criterion supplies "
                            + "the factorization iff fiber-constancy step, which is exactly the "
                            + "negation of the witness predicate.")),
                    Paragraph(Text(
                        "This formalizes the finite combinatorial kernel of theorem/40.1. "
                            + "The normative choice between control-based and outcome-based "
                            + "evaluation is intentionally not represented."))),
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

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Formula()
    {
        Formula state = F.Id("X");
        Formula controlType = F.Id("B");
        Formula evaluationType = F.Id("L");
        Formula control = F.Id("C");
        Formula evaluation = F.Id("J");
        Formula factor = F.Id("d");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula stateTo(Formula codomain) => Arrow(state, codomain);
        Formula witness = Seq(
            Exists, Sp, left, Comma, Sp, right, Comma, Esc,
            Apply(control, left), Sp, Eq, Sp, Apply(control, right), Sp, Land, Sp,
            Apply(evaluation, left), Sp, Neq, Sp, Apply(evaluation, right));
        Formula principle = Seq(
            Exists, Sp, factor, Colon, Sp, Arrow(controlType, evaluationType), Comma, Sp,
            evaluation, Sp, Eq, Sp, Compose(factor, control));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, controlType, Comma, Sp, evaluationType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Fintype", state), Comma, Sp,
            Typeclass("Fintype", controlType), Comma, Sp,
            Typeclass("Fintype", evaluationType), Comma, Sp,
            Typeclass("Nonempty", state), Comma, Esc,
            control, Colon, Sp, stateTo(controlType), Comma, Sp,
            evaluation, Colon, Sp, stateTo(evaluationType), Comma, Esc,
            principle, Sp, Iff, Sp, Neg, Sp, Exists, Sp, left, Comma, Sp, right, Comma, Esc,
            Apply(control, left), Sp, Eq, Sp, Apply(control, right), Sp, Land, Sp,
            Apply(evaluation, left), Sp, Neq, Sp, Apply(evaluation, right), Dot));
    }
}
