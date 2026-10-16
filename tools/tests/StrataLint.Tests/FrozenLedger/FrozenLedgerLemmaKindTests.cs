using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("", false)]
    [InlineData("private ", false)]
    [InlineData("@[simp] ", false)]
    [InlineData("", true)]
    [InlineData("private ", true)]
    [InlineData("@[simp] ", true)]
    public void MathlibReanchorRecognizesLemmaAsCompiledTheorem(string prefix, bool changeStatement)
    {
        var source = "namespace N\n" + prefix + "lemma a : True := by exact True.intro\nend N\n";
        var baseline = ModuleWithReport("A", source, "old elaborated theorem", declarations: ["N.a"]);
        var candidate = baseline with
        {
            Source = changeStatement
                ? source.Replace(": True", ": False", StringComparison.Ordinal)
                : source.Replace("exact True.intro", "trivial", StringComparison.Ordinal),
            StatementMaterial = "new elaborated theorem",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeStatement, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesDefinitionDependenciesOfLemma(bool changeDefinition)
    {
        var source = "def premise : Prop := True\nlemma a : premise := by exact True.intro\n";
        var baseline = ModuleWithReport("A", source, "old elaborated theorem");
        var candidate = baseline with
        {
            Source = source.Replace("exact True.intro", "trivial", StringComparison.Ordinal)
                .Replace(":= True", changeDefinition ? ":= False" : ":= True", StringComparison.Ordinal),
            StatementMaterial = "new elaborated theorem",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeDefinition, result.Authorized);
    }

    [Theory]
    [InlineData("def")]
    [InlineData("opaque")]
    public void MathlibReanchorRejectsLemmaRecordedAsNonTheorem(string kind)
    {
        var baseline = ModuleWithReport("A", "lemma a : True := by trivial\n", "old material", kind: kind);
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [baseline with { StatementMaterial = "new material" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("def a : True := True.intro\n")]
    [InlineData("opaque a : True := True.intro\n")]
    [InlineData("axiom a : True\n")]
    public void MathlibReanchorRejectsNonTheoremRecordedAsTheorem(string source)
    {
        var baseline = ModuleWithReport("A", source, "old theorem material");
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [baseline with { StatementMaterial = "new theorem material" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
