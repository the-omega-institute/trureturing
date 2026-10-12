using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("7", true)]
    [InlineData("8", false)]
    public void MathlibReanchorRetainsDataInTypesContainingEquality(string value, bool accepted)
    {
        const string original = "def a : Nat := by\n  have h : (0 : Nat) = 0 ×' Nat := by\n    exact ⟨rfl, 7⟩\n  exact h.2\n";
        var candidate = original.Replace("rfl, 7", "rfl, " + value, StringComparison.Ordinal);
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old Nat", kind: "def"), Module("B")],
            [ModuleWithReport("A", candidate, "new Nat", kind: "def"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.Equal(accepted, result.Authorized);
    }

    [Theory]
    [InlineData("a.eq_def", "True", true)]
    [InlineData("a.eq_def", "False", false)]
    [InlineData("a_assoc", "True", true)]
    [InlineData("a_assoc", "False", false)]
    public void MathlibReanchorGeneratedNamesRetainTheWholeSourceProposition(
        string generatedName, string proposition, bool accepted)
    {
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", "theorem a : True := by exact True.intro\n",
                "old generated", declarations: [generatedName]), Module("B")],
            [ModuleWithReport("A", "theorem a : " + proposition + " := by trivial\n",
                "new generated", declarations: [generatedName]), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.Equal(accepted, result.Authorized);
    }

    [Theory]
    [InlineData("/- declaration -/ ", "")]
    [InlineData("public ", "")]
    [InlineData("@[expose] public section\n", "end\n")]
    [InlineData("noncomputable section\n", "end\n")]
    [InlineData("  ", "")]
    [InlineData("set_option autoImplicit false in ", "")]
    public void MathlibReanchorReadsCommandPrefixesWithoutLosingTheStatement(
        string prefix, string suffix)
    {
        var original = prefix + "lemma a : True := by exact True.intro\n" + suffix;
        var candidate = prefix + "lemma a : True := by trivial\n" + suffix;
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old True"), Module("B")],
            [ModuleWithReport("A", candidate, "new True"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);

        var weakened = ValidateMathlibReanchor(
            [ModuleWithReport("A", prefix + "lemma a : False := by contradiction\n" + suffix,
                "old False"), Module("B")],
            [ModuleWithReport("A", candidate, "new True"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(weakened.Recognition);
        Assert.False(weakened.Authorized);
    }

    [Theory]
    [InlineData("7", false)]
    [InlineData("8", false)]
    public void MathlibReanchorRefusesUnclassifiedLocalEqualityProofBodyChanges(string value, bool accepted)
    {
        const string original = "def a : Nat := by\n  have h : (0 : Nat) = 0 := by\n    rfl\n  exact 7\n";
        var candidate = "def a : Nat := by\n  have h : (0 : Nat) = 0 := by\n    simp\n  exact " + value + "\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", original, "old Nat", kind: "def"), Module("B")],
            [ModuleWithReport("A", candidate, "new Nat", kind: "def"), Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.Equal(accepted, result.Authorized);
    }
}
