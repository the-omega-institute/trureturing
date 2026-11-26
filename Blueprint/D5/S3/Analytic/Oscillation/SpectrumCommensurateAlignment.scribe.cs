using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumCommensurateAlignmentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A logarithmic square tail can coexist with frequent full sine alignment.",
        H("Frequent Full Alignment with a Logarithmic Square Tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-logarithmic-full-alignment"),
                DeclarationHandle.Create(Owner + ".exists_logarithmic_full_alignment"),
                H("Full alignment in every interval of logarithmic length"),
                StatementSource.FromAuthor(Model()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use blocks between 4·2ⁿ and 8·2ⁿ. In block n let q be the largest power "
                        + "of five at most n+1. Put q·2ⁿ distinct frequencies at offsets "
                        + "(4k+1)/q from the lower boundary, and divide total weight 2n+1 equally "
                        + "among them. The frequencies strictly inside each block give local "
                        + "finiteness and distinctness.")),
                    Paragraph(Text(
                        "A cutoff in block n contains the first n complete blocks and some of "
                        + "block n. Their weights bound the inclusive mass between n² and (n+1)². "
                        + "The squared weight of a complete block is at most 20(n+1)/2ⁿ, "
                        + "the consecutive difference of 40(n+2)/2ⁿ. Summing from the block "
                        + "containing X bounds the tail by a constant times log X/X for "
                        + "every finite upper cutoff T ≥ X.")),
                    Paragraph(Text(
                        "At a cutoff in block N, each earlier denominator divides q in block N "
                        + "with quotient congruent to one modulo four. Multiplying each retained "
                        + "frequency by q therefore gives an integer congruent to one modulo four. "
                        + "All retained sines equal one at πq/2 and at every translate of that "
                        + "time by an integer multiple of 2πq, simultaneously at every smaller "
                        + "inclusive cutoff. The estimate q+1 ≤ log T/log 2 puts at least 2π "
                        + "between that period and the stated interval length.")),
                    Paragraph(Text(
                        "Thus the logarithmic mass and square-tail laws permit a spectrum "
                        + "that reaches full mass in every sufficiently long window. The "
                        + "construction concerns a comparison spectrum. The window theorem "
                        + "with rational linear independence is available in "),
                        Ref("D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow"
                            + ".eventual_logarithmic_missing_window"))),
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

    private static Formula Model()
    {
        var s = F.Id("S");
        var w = F.Id("w");
        var t = F.Id("T");
        var a = F.Id("A");
        var q = F.Id("q");
        var m = F.Id("m");
        var x = F.Id("X");
        var index = Call("index", s);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var integers = Seq(Mathbb, Grp(F.Id("Z")));
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var time = Add(new Formula.Fraction(Multiply(Pi, q), D(2)),
            Multiply(m, Multiply(D(2), Multiply(Pi, q))));
        var right = Add(a, Multiply(new Formula.Fraction(Multiply(D(2), Pi), Call("log", D(2))),
            Call("log", t)));
        var visits = Bind(FormulaQuantifier.ForAll, "A", reals,
            Bind(FormulaQuantifier.Exists, "m", integers, And(Less(a, time), Less(time, right))));
        var alignment = Bind(FormulaQuantifier.ForAll, "m", integers,
            Bind(FormulaQuantifier.ForAll, "X", reals,
                new Formula.Logic(AtMost(x, t), FormulaLogicOperator.Implies,
                    new Formula.Relation(Call("sine", s, w, x, time),
                        FormulaRelationOperator.Equal, Call("mass", s, w, x)))));
        var bound = AtMost(Add(q, D(1)), new Formula.Fraction(Call("log", t), Call("log", D(2))));
        var window = new Formula.Logic(AtMost(D(5), t), FormulaLogicOperator.Implies,
            And(Less(D(0), Call("mass", s, w, t)),
                Bind(FormulaQuantifier.Exists, "q", naturals,
                    And(Less(D(0), q), And(bound, And(alignment, visits))))));
        var recurrence = Bind(FormulaQuantifier.ForAll, "T", reals, window);
        var positive = Bind(FormulaQuantifier.ForAll, "j", index, Less(D(0), Call("w", F.Id("j"))));
        return Disp(Bind(FormulaQuantifier.Exists, "S", F.Id("Spectrum"),
            Bind(FormulaQuantifier.Exists, "w", Seq(index, Sp, To, Sp, reals),
                And(Call("Infinite", index), And(positive,
                    And(Call("HasLogSquaredMass", s, w),
                        And(Call("HasLogarithmicSquareTail", s, w), recurrence)))))));
    }
}
