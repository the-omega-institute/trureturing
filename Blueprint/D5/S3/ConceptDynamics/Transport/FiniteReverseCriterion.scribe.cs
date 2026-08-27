using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class FiniteReverseCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Empty carry yields a unique descent on the effective image.",
        H("Finite Reverse Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-reverse-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/FiniteReverseCriterion."
                        + "finite_reverse_criterion"),
                H("Empty carry determines the effective-image descent"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X, B_C, and B_D be finite types with decidable equality, let "
                            + "F map X to a process codomain Y, and let q_C and q_D be the "
                            + "current and future readouts. Carry consists exactly of pairs "
                            + "identified by q_C whose future readouts after F differ.")),
                    Paragraph(Text(
                        "If the carry type is empty, there is a unique map from the realized "
                            + "range of q_C to B_D. On every source state, this map sends its "
                            + "effective current value to q_D(F(x)), so the image-restricted "
                            + "process/readout square commutes.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the canonical Set.rangeFactorization and "
                            + "Set.rangeSplitting maps used by the proof. Empty carry makes the "
                            + "chosen representative irrelevant, while every range element's "
                            + "source witness proves uniqueness. Repository and pinned-library "
                            + "searches found no existing theorem packaging these facts.")),
                    Paragraph(Text(
                        "This formalizes exactly theorem/13.2 of formal-concept-dynamics, atom "
                            + "generic-residual-88ab11467c06c97a9dd12a0627951364cfe0c6a897813"
                            + "bf9209fc113283a304e. No claim about infinite constructive models "
                            + "or the neighboring quantitative defect is included."))),
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
        Formula current = new Formula.Subscript(F.Id("q"), F.Id("C"));
        Formula future = new Formula.Subscript(F.Id("q"), F.Id("D"));
        Formula descent = Seq(Overline, Grp(process));
        Formula x = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula range = Apply(Seq(Operatorname, Grp(F.Id("range"))), current);
        Formula carry = Apply(Seq(Operatorname, Grp(F.Id("Carry"))), process, current, future);
        Formula emptyCarry = Call("IsEmpty", carry);
        Formula effectiveValue = Apply(
            Seq(Operatorname, Grp(F.Id("rangeFactorization"))), current, x);

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
            emptyCarry, Sp, Rightarrow, Esc,
            Exists, Bang, Sp, descent, Colon, Sp, Arrow(range, futureType), Comma, Esc,
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(descent, effectiveValue), Sp, Eq, Sp,
            Apply(future, Apply(process, x)), Dot));
    }
}
