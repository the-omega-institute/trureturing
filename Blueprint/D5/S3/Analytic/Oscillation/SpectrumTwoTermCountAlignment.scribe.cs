using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumTwoTermCountAlignmentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumTwoTermCountAlignment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded two-term count discrepancy can coexist with frequent full sine alignment.",
        H("Bounded Two-Term Count Discrepancy and Full Phase Alignment"),
        Blocks(
            Paragraph(Text(
                "The count, sine score and mass use inclusive cutoffs. Eventually means for all sufficiently "
                + "large real thresholds. Write u(q,m) = πq/2 + 2πqm.")),
            Describe.Lean(
                DescribeId.Create("exists-two-term-count-alignment"),
                DeclarationHandle.Create(Owner + ".exists_two_term_count_alignment"),
                H("Harmonic weights and full alignment at a bounded count discrepancy"),
                StatementSource.FromAuthor(Model()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Scale the grid of "), Ref("D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment"
                            + ".exists_logarithmic_full_alignment"),
                        Text(" by 1/21. Start at the lower boundary of block six. Write F for the "
                            + "displayed smooth counting function. Its derivative is log(t/(2π))/(2π). "
                            + "The increase of F between successive grid points is in [0,1), including "
                            + "the gaps crossing block boundaries.")),
                    Paragraph(Text(
                        "Keep a grid point exactly when the floor of F increases there. All retained "
                        + "frequencies have multiplicity one. Summing the floor increments telescopes to "
                        + "the floor of F at the last grid point at or below the cutoff, minus the floor "
                        + "of F at the initial boundary. Before the first grid point the initial boundary "
                        + "serves as predecessor. The floor and the remaining gap contribute less than "
                        + "two to the absolute count error after removing the initial offset.")),
                    Paragraph(Text(
                        "Use the count in the partial-summation estimate for harmonic phase mass "
                        + "and the inverse-square tail bound. The closed and open counts differ by "
                        + "at most one since the frequencies are distinct and have unit multiplicity. "
                        + "The chosen weights are positive and bounded above by the inverse frequency.")),
                    Paragraph(Text(
                        "For a cutoff in block n take q equal to 21 times the grid denominator of that "
                        + "block. Every grid frequency at or below the cutoff, multiplied by q, is "
                        + "an integer congruent to one modulo four. This also holds on the retained "
                        + "subset, so all its sines equal one at u(q,m) simultaneously for all smaller "
                        + "cutoffs. The interval length exceeds the progression period by at least 2π.")),
                    Paragraph(Text(
                        "The comparison spectrum matches the two-term count with a uniformly bounded "
                        + "error and retains full alignment. Applying a finite-resolution cancellation "
                        + "argument to actual zeta ordinates still requires estimates for their additive "
                        + "phase relations."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Eventually(Formula variable, Formula body) =>
        Call("Eventually", Seq(Open, variable, Sp, Mapsto, Sp, body, Close), F.Id("atTop"));

    private static Formula Model()
    {
        var s = F.Id("S");
        var w = F.Id("w");
        var t = F.Id("T");
        var a = F.Id("A");
        var q = F.Id("q");
        var m = F.Id("m");
        var x = F.Id("X");
        var j = F.Id("j");
        var error = F.Id("D");
        var index = Call("index", s);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var integers = Seq(Mathbb, Grp(F.Id("Z")));
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var time = Call("u", q, m);
        var scaledLog = Call("log", Multiply(D(2, 1), t));
        var logTwo = Call("log", D(2));
        var right = Add(a, Multiply(new Formula.Fraction(Multiply(D(4, 2), Pi), logTwo), scaledLog));
        var visits = Bind(FormulaQuantifier.ForAll, "A", reals,
            Bind(FormulaQuantifier.Exists, "m", integers, And(Less(a, time), Less(time, right))));
        var alignment = Bind(FormulaQuantifier.ForAll, "m", integers,
            Bind(FormulaQuantifier.ForAll, "X", reals,
                new Formula.Logic(AtMost(x, t), FormulaLogicOperator.Implies,
                    Equal(Call("sine", s, w, x, time), Call("mass", s, w, x)))));
        var bound = AtMost(Add(q, D(1)), Multiply(D(2, 1), new Formula.Fraction(scaledLog, logTwo)));
        var recurrence = Eventually(t, And(Less(D(0), Call("mass", s, w, t)),
            Bind(FormulaQuantifier.Exists, "q", naturals,
                And(Less(D(0), q), And(bound, And(alignment, visits))))));

        var gamma = Seq(GammaLower, Open, j, Close);
        var weight = new Formula.Fraction(gamma,
            Add(new Formula.Fraction(D(1), D(4)), new Formula.Power(Seq(Open, gamma, Close), D(2))));
        var weights = Bind(FormulaQuantifier.ForAll, "j", index,
            And(Equal(Call("mult", s, j), D(1)), Equal(Call("w", j), weight)));
        var scaledCutoff = new Formula.Fraction(t, Multiply(D(2), Pi));
        var mainTerm = Multiply(scaledCutoff, Seq(Open, Call("log", scaledCutoff), Minus, D(1), Close));
        var discrepancy = new Formula.Absolute(Seq(Call("N", s, t), Minus, mainTerm));
        var count = Bind(FormulaQuantifier.Exists, "D", reals,
            And(AtMost(D(0), error), Eventually(t, AtMost(discrepancy, error))));
        return Disp(Bind(FormulaQuantifier.Exists, "S", F.Id("Spectrum"),
            Bind(FormulaQuantifier.Exists, "w", Seq(index, Sp, To, Sp, reals),
                And(Call("Infinite", index), And(weights, And(count,
                    And(Call("HasLogSquaredMass", s, w),
                        And(Call("HasLogarithmicSquareTail", s, w), recurrence))))))));
    }
}
