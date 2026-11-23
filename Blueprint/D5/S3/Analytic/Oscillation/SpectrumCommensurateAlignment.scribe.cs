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
                        + "time by an integer multiple of 2πq. Since q ≤ N+1, the distance from "
                        + "any real start to the next member of this progression is less than "
                        + "(2π/log 2) log T.")),
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
        var c = F.Id("C");
        var t = F.Id("T");
        var a = F.Id("A");
        var u = F.Id("u");
        var index = Call("index", s);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var mass = Call("mass", s, w, t);
        var sine = Call("sine", s, w, t, u);
        var right = Seq(a, Sp, Plus, Sp, Multiply(c, Call("log", t)));
        var aligned = Bind(FormulaQuantifier.Exists, "u", reals,
            And(AtMost(a, u), And(Less(u, right),
                new Formula.Relation(sine, FormulaRelationOperator.Equal, mass))));
        var window = new Formula.Logic(AtMost(D(5), t), FormulaLogicOperator.Implies,
            And(Less(D(0), mass), Bind(FormulaQuantifier.ForAll, "A", reals, aligned)));
        var recurrence = Bind(FormulaQuantifier.Exists, "C", reals,
            And(Less(D(0), c), Bind(FormulaQuantifier.ForAll, "T", reals, window)));
        var positive = Bind(FormulaQuantifier.ForAll, "j", index, Less(D(0), Call("w", F.Id("j"))));
        return Disp(Bind(FormulaQuantifier.Exists, "S", F.Id("Spectrum"),
            Bind(FormulaQuantifier.Exists, "w", Seq(index, Sp, To, Sp, reals),
                And(Call("Infinite", index), And(positive,
                    And(Call("HasLogSquaredMass", s, w),
                        And(Call("HasLogarithmicSquareTail", s, w), recurrence)))))));
    }
}
