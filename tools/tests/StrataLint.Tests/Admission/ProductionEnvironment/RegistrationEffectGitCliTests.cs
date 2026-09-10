namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData("='", false)]
    [InlineData(",", false)]
    [InlineData("='", true)]
    [InlineData(",", true)]
    public void GitCliExplicitSeparatorMetadataPreservesCharContext(string separator, bool modified)
    {
        var prefix = "import Lean\n"
            + $"syntax \"eqList\" sepBy1(term, \"{separator}\", \",\") : term\n"
            + "example : ')' =')' := by decide\n";
        CheckAnonymousSource("decide", 0, prefix, modified, prepareContext: true);
    }

    [Theory]
    [InlineData("='", false)]
    [InlineData("safe", false)]
    [InlineData("='", true)]
    [InlineData("safe", true)]
    public void GitCliNotationExpansionStringPreservesCharContext(string expansion, bool modified)
    {
        var prefix = "import Init\n"
            + $"notation \"attrWitness\" => \"{expansion}\"\n"
            + "attribute [simp] Nat.add_zero\nexample : ')' =')' := by decide\n";
        CheckAnonymousSource("decide", 0, prefix, modified, prepareContext: true);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void GitCliCoreInstanceCharCompilesPreparesAndAdmitsWithEmptyReport(bool attribute, bool modified)
    {
        var prefix = "import Init\n"
            + (attribute ? "attribute [local instance] instInhabitedNat\n" : "")
            + "example : ')' =')' := by decide\n";
        CheckAnonymousSource("decide", 0, prefix, modified, prepareContext: true);
    }
}
