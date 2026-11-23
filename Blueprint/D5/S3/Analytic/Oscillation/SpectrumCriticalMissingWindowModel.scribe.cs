using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumCriticalMissingWindowModelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite positive-weight spectrum realizes both mass hypotheses at once.",
        H("An Infinite Spectrum for the Critical Missing-Window Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-infinite-critical-model"),
                DeclarationHandle.Create(Owner + ".exists_infinite_critical_model"),
                H("An infinite spectrum with independent frequencies and positive weights"),
                StatementSource.FromAuthor(Model()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose countably many members of a rational basis of the reals. "
                        + "Multiply the nth member by a nonzero rational so that its ordinate "
                        + "lies strictly between the fourth roots of n+1 and n+2. This is "
                        + "possible by rational density and preserves rational linear independence. "
                        + "The intervals order the ordinates and give local finiteness.")),
                    Paragraph(Text(
                        "Take w(n) = log²(n+2) − log²(n+1), which is positive. If n is the "
                        + "last index below or at T, the mass telescopes to log²(n+2). "
                        + "The interval bounds give n+1 < T⁴ < n+3. Consequently "
                        + "|log(n+2) − 4 log T| ≤ 1, yielding a squared-logarithmic "
                        + "coefficient of 16 and error at most 9(1+log T) eventually.")),
                    Paragraph(Text(
                        "The log increment is at most 1/(n+1), and the sum of the two "
                        + "logs is at most 32(n+1)^(1/8). Thus w(n) ≤ 32(n+1)^(−7/8), "
                        + "and (n+1)^(1/2)w(n)² has finite sum by comparison with a "
                        + "series of exponent 5/4. For ordinates above X ≥ 1, "
                        + "X² ≤ 2(n+1)^(1/2). The square tail is therefore O(X⁻²), "
                        + "uniformly in the finite upper cutoff. "),
                        Ref("D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-infinite-logarithmic-model"),
                DeclarationHandle.Create(Owner + ".exists_infinite_logarithmic_model"),
                H("An infinite model for the logarithmic waiting gain"),
                StatementSource.FromAuthor(Model("HasLogarithmicSquareTail")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the same rationally independent fourth-root bins and strictly "
                    + "positive weights. Their square tail is at most B/X² for a "
                    + "fixed B > 0 whenever X ≥ 1. Once log X ≥ 1, this is at most "
                    + "B log X/X uniformly in T ≥ X. "),
                    Ref("D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow"
                        + ".eventual_logarithmic_missing_window"))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Model(string tailCondition = "HasSmallSquareTail")
    {
        var s = F.Id("S");
        var w = F.Id("w");
        var index = Call("index", s);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var rats = Seq(Mathbb, Grp(F.Id("Q")));
        var positive = Bind(FormulaQuantifier.ForAll, "j", index,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("w", F.Id("j"))));
        return Disp(Bind(FormulaQuantifier.Exists, "S", F.Id("Spectrum"),
            Bind(FormulaQuantifier.Exists, "w", Seq(index, Sp, To, Sp, reals),
                And(Call("Infinite", index), And(positive,
                    And(Call("LinearIndependent", rats, Call("gamma", s)),
                        And(Call("HasLogSquaredMass", s, w), Call(tailCondition, s, w))))))));
    }
}
