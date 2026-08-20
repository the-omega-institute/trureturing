using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class CounterfactualFairnessDoesNotImplyGroupParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Protected-attribute invariance can coexist with unequal observed group decision rates.",
        H("Counterfactual Fairness Does Not Imply Group Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("counterfactual-fairness-does-not-imply-group-parity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FiniteCountermodels/"
                        + "CounterfactualFairnessDoesNotImplyGroupParity."
                        + "counterfactual_fairness_does_not_imply_group_parity"),
                H("Counterfactual fairness need not imply group parity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The decision reads only qualification r. Every protected intervention replaces "
                            + "p by a chosen Boolean value g while retaining r, so the decision is "
                            + "pointwise invariant for every state and intervention value.")),
                    Paragraph(Text(
                        "The explicit two-point population is supported on r=p. Both protected groups "
                            + "are nonempty, making the conditional counting denominators one. The group "
                            + "with p=0 has decision rate zero and the group with p=1 has decision rate one.")),
                    Paragraph(Text(
                        "The rate is derived from finite member and positive-member counts rather than "
                            + "installed as a constant. Repository and pinned-library searches found no "
                            + "existing theorem joining counterfactual invariance to these group-rate clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Open, Seq(arguments), Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula g = F.Id("g");
        Formula j = F.Id("J");
        Formula intervention = F.Id("I");
        Formula population = F.Id("P");
        Formula group = F.Id("G");
        Formula rate = Rho;
        Formula state = Pair(p, r);
        Formula zero = Pair(D(0), D(0));
        Formula one = Pair(D(1), D(1));
        Formula groupZero = Sub(group, D(0));
        Formula groupOne = Sub(group, D(1));
        Formula rateZero = Sub(rate, D(0));
        Formula rateOne = Sub(rate, D(1));
        Formula counterfactual = Seq(
            Forall, Sp, g, Comma, Sp, p, Comma, Sp, r, Comma, Sp,
            Apply(intervention, g, state), Eq, Pair(g, r), Sp, Land, Sp,
            Apply(j, Apply(intervention, g, state)), Eq, Apply(j, state));
        Formula diagonalSupport = Seq(
            Forall, Sp, p, Comma, Sp, r, Comma, Sp,
            state, Sp, InMacro, Sp, population, Sp, Rightarrow, Sp, r, Eq, p);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            population, Eq, new Formula.SetLiteral([zero, one]), Comma, RowBreak,
            counterfactual, Comma, RowBreak,
            diagonalSupport, Comma, RowBreak,
            groupZero, Sp, Neq, Sp, Emptyset, Sp, Land, Sp,
            groupOne, Sp, Neq, Sp, Emptyset, Comma, RowBreak,
            rateZero, Eq, D(0), Sp, Land, Sp, rateOne, Eq, D(1), Sp, Land, Sp,
            rateZero, Sp, Neq, Sp, rateOne, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
