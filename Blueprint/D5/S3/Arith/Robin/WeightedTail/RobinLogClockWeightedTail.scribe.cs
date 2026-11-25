using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.WeightedTail;

internal sealed class RobinLogClockWeightedTailDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/WeightedTail/RobinLogClockWeightedTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted Mangoldt tail at the logarithm of an integer",
        H("A strict bound for the logarithmic Robin margin"),
        Blocks(
            Describe.Lean(DescribeId.Create("log-clock-weighted-tail-below-margin"),
                DeclarationHandle.Create(Module + "weightedTail_lt_robinLogMargin"),
                H("The full weighted tail and the divisor sum"),
                StatementSource.FromAuthor(Comparison()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every integer n>5040, put y=log(n). "
                        + "The complete weighted Chebyshev tail at y is strictly below "
                        + "the logarithmic Robin margin of n.")),
                    Paragraph(Text("At a positive prime valuation, the logarithmic Euler factor "
                        + "is strictly below its finite Mangoldt sum. Sum this bound over "
                        + "the prime factors of n, retaining multiplicity.")),
                    Paragraph(Text("Subtract the same cost per unit from each divisor's benefit. "
                        + "The signed terms are nonnegative through y and nonpositive above y. "
                        + "The divisor cost is exactly log(n) and the cutoff cost is ψ(y). "
                        + "Their difference cancels the boundary term in the complete Mertens ledger."))),
                DescribeRole.Theorem))));

    private static Formula Comparison()
    {
        var n = F.Id("n");
        var log = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [n]);
        return Disp(new Formula.Relation(
            new Formula.FunctionCall(FormulaIdentifier.Create("J"), [log]),
            FormulaRelationOperator.LessThan,
            new Formula.FunctionCall(FormulaIdentifier.Create("robinLogMargin"), [n])));
    }
}
