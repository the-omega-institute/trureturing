using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class CoupledSevenBudgetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two displayed prime-palette envelopes cannot both reach one when "
            + "their low allocations share one unit pool and their high allocations "
            + "share a separate unit pool. All four allocations may be real.",
        H("Incompatible Coupled Seven Budgets"),
        Blocks(
            Entry("smallPalette", "The first ordinary-prime palette",
                "The first palette is {5,11,13,17,19,23,29,31,37,41,43}. "
                    + "The shared prime seven is excluded from this ordinary palette.",
                DescribeRole.Definition),
            Entry("tailPalette", "The second palette's additional primes",
                "The additional primes are {47,53,59,61,67,71}.",
                DescribeRole.Definition),
            Entry("otherPalette", "One partition determines both palettes",
                "For a subset A of the first palette, the second palette consists "
                    + "of the first palette minus A, together with all additional primes.",
                DescribeRole.Definition),
            Entry("ordinaryWeight", "Prime weights",
                "Each ordinary prime p has rational weight 1/(p-3).",
                DescribeRole.Definition),
            Entry("ordinaryProduct", "Product of the ordinary contributions",
                "The ordinary product is the product of 1+1/(p-3) over the selected primes.",
                DescribeRole.Definition),
            Entry("budget", "The coarse rational budget",
                "For parameters kappa and b, the budget is (2+kappa) times "
                    + "((1+b) times the ordinary product minus one), minus twice "
                    + "the sum of b and the ordinary prime weights.",
                DescribeRole.Definition),
            Entry("gain", "The shared-axis coefficient",
                "The gain is (2+kappa) times (the ordinary product minus one).",
                DescribeRole.Definition),
            Entry("rawDemand", "The rational endpoint demand",
                "At low allocation t, the raw high-allocation demand is "
                    + "((1-budget(kappa,0,A)) times (5-t) minus gain(kappa,A)) "
                    + "divided by kappa. It is not truncated at zero.",
                DescribeRole.Definition),
            Entry("partition_obstruction", "Every partition has an obstruction",
                "For every subset A of the first palette, either a coarse budget with shared weight 1/4 "
                    + "is strictly below one, or the sum of the two raw demands "
                    + "is strictly above one at both complementary allocation endpoints. "
                    + "The first envelope uses kappa=1/2 and the second uses kappa=1/3.",
                DescribeRole.Theorem),
            Entry("envelope", "The envelope with real allocations",
                "For real low and high allocations t and v, the envelope is "
                    + "budget(kappa,0,A) plus (gain(kappa,A)+kappa times v)/(5-t), "
                    + "with the rational coefficients interpreted in the reals.",
                DescribeRole.Definition),
            Entry("demand", "The real demand",
                "The same raw-demand expression is evaluated at a real low allocation. "
                    + "The palette coefficients remain the specified rational constants.",
                DescribeRole.Definition),
            Entry("claim", "Simultaneous feasibility",
                "There exists a subset A of the first palette and four nonnegative real allocations "
                    + "t0,t1,v0,v1 such that t0+t1 is at most one, v0+v1 is at most "
                    + "one, and both corresponding envelopes are at least one.",
                DescribeRole.Definition),
            Entry("result", "The two real budgets are incompatible",
                "Simultaneous feasibility is false. A failing coarse bound gives "
                    + "an immediate contradiction. Otherwise increase the second low "
                    + "allocation to 1-t0, which enlarges its envelope because its "
                    + "numerator is nonnegative. The affine sum of their required "
                    + "lower bounds is then strictly above one, contradicting their "
                    + "joint unit pool. This result concerns the stated scalar "
                    + "inequalities; deriving them from an arithmetic covering family "
                    + "is a separate implication.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string heading, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("coupled-seven-budget-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
