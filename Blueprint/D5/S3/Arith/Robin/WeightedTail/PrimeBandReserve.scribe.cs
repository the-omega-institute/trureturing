using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.WeightedTail;

internal sealed class PrimeBandReserveDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-band reserve for the logarithmic Robin slack",
        H("A bound in terms of the number of primes in the band"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-band"),
                DeclarationHandle.Create(Module + "primeBand"),
                H("The finite prime band"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real y, the band is the finite set of primes "
                    + "at most the natural floor of 2√y, excluding the primes at most "
                    + "the natural floor of √(2y)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-band-reserve-below-robin-log-slack"),
                DeclarationHandle.Create(Module + "primeBand_reserve_le_robinLogSlack"),
                H("Each prime contributes at least 1/(16y)"),
                StatementSource.FromAuthor(Comparison()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a natural number n with y = log(n) ≥ 16, let B(y) consist "
                        + "of the primes p with √(2y) < p ≤ 2√y. Let J(y) be the complete "
                        + "weighted Chebyshev tail.")),
                    Paragraph(Text("The complete Mertens ledger cancels the boundary term against "
                        + "the signed difference of the divisor and cutoff Mangoldt costs. "
                        + "The Robin slack equals the sum of the local Euler gaps, the signed weights "
                        + "of missing terms through y, and the negated signed weights of extra terms above y. "
                        + "Each of these sums is nonnegative term by term.")),
                    Paragraph(Text("A band prime of valuation zero contributes its missing first power. "
                        + "A prime of valuation one contributes its local Euler gap. A prime of valuation "
                        + "at least two contributes its square above the cutoff. Each contribution "
                        + "is at least 1/(16y), and the primes use distinct terms in these sums."))),
                DescribeRole.Theorem))));

    private static Formula Comparison()
    {
        var n = F.Id("n");
        var y = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [n]);
        var band = new Formula.FunctionCall(FormulaIdentifier.Create("B"), [y]);
        var reserve = new Formula.Fraction(new Formula.Absolute(band), Multiply(D(1, 6), y));
        var margin = new Formula.FunctionCall(FormulaIdentifier.Create("robinLogMargin"), [n]);
        var tail = new Formula.FunctionCall(FormulaIdentifier.Create("J"), [y]);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(
                new Formula.Relation(D(1, 6), FormulaRelationOperator.LessThanOrEqual, y),
                FormulaLogicOperator.Implies,
                new Formula.Relation(reserve, FormulaRelationOperator.LessThanOrEqual,
                    Subtract(margin, tail)))));
    }
}
