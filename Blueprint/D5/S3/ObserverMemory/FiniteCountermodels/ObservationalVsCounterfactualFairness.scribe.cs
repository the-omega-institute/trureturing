using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class ObservationalVsCounterfactualFairnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qualification factorization on admitted states need not survive a coupled intervention.",
        H("Observational Fairness Does Not Imply Counterfactual Fairness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observational-fairness-does-not-imply-counterfactual-fairness"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FiniteCountermodels/"
                        + "ObservationalVsCounterfactualFairness."
                        + "observational_fairness_does_not_imply_counterfactual_fairness"),
                H("Observational fairness need not be counterfactual fairness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admitted population contains exactly the two diagonal Boolean states. "
                            + "Qualification and decision both read the second coordinate, so the "
                            + "decision factors through qualification via the identity Boolean map.")),
                    Paragraph(Text(
                        "The intervention flips the protected bit and causally resets the qualification "
                            + "to that new bit. It therefore sends (0,0) to (1,1), changing the named "
                            + "decision from zero to one. This explicit witness refutes pointwise "
                            + "counterfactual invariance while preserving observational factorization.")),
                    Paragraph(Text(
                        "Searches of D5 and pinned Mathlib found factorization machinery but no finite "
                            + "fairness predicate or theorem combining these admission and intervention "
                            + "clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Open, Seq(arguments), Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula BoolSet() => new Formula.SetLiteral([D(0), D(1)]);

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula g = F.Id("g");
        Formula j = F.Id("J");
        Formula intervention = F.Id("I");
        Formula admission = F.Id("Adm");
        Formula state = Pair(p, r);
        Formula zero = Pair(D(0), D(0));
        Formula one = Pair(D(1), D(1));
        Formula factorization = Seq(
            Exists, Sp, g, Colon, Sp, BoolSet(), Sp, To, Sp, BoolSet(), Comma, Sp,
            Forall, Sp, p, Comma, Sp, r, Comma, Sp,
            state, Sp, InMacro, Sp, admission, Sp, Rightarrow, Sp,
            Apply(j, state), Eq, Apply(g, r));
        Formula counterfactual = Seq(
            Forall, Sp, p, Comma, Sp, r, Comma, Sp,
            state, Sp, InMacro, Sp, admission, Sp, Rightarrow, Sp,
            Apply(j, Apply(intervention, state)), Eq, Apply(j, state));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            admission, Eq, new Formula.SetLiteral([zero, one]), Comma, RowBreak,
            factorization, Comma, RowBreak,
            zero, Sp, InMacro, Sp, admission, Sp, Land, Sp,
            one, Sp, InMacro, Sp, admission, Comma, RowBreak,
            Apply(j, zero), Eq, D(0), Sp, Land, Sp,
            Apply(j, one), Eq, D(1), Comma, RowBreak,
            Apply(intervention, zero), Eq, one, Sp, Land, Sp,
            Apply(j, Apply(intervention, zero)), Eq, D(1), Comma, RowBreak,
            Neg, Sp, Grp(counterfactual), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
