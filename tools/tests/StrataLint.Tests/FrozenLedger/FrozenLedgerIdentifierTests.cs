using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("divide?", false)]
    [InlineData("divide?", true)]
    [InlineData("lowerBound?", false)]
    [InlineData("lowerBound?", true)]
    [InlineData("value!", false)]
    [InlineData("value!", true)]
    public void MathlibReanchorPreservesIdentifierSuffixDefinitionBodies(string name, bool mutate)
    {
        var source = $"def {name} : Nat := 1\n";
        var baseline = ModuleWithReport("A", source, "old elaborated definition",
            declarations: [name], kind: "def");
        var candidate = baseline with
        {
            Source = mutate ? source.Replace(":= 1", ":= 2", StringComparison.Ordinal) : source,
            StatementMaterial = "new elaborated definition",
        };
        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")], candidateModules: [candidate, Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorResolvesRelativeQualifiedTheoremWithinNamespace(bool mutate)
    {
        const string source = "namespace Lambda\ninductive LMonoTy where\n  | unit\n"
            + "theorem LMonoTy.induct : True := by exact True.intro\nend Lambda\n";
        var baseline = ModuleWithReport("A", source, "old elaborated theorem",
            declarations: ["Lambda.LMonoTy.induct"]);
        var candidate = baseline with
        {
            Source = mutate ? source.Replace(": True", ": False", StringComparison.Ordinal)
                : source.Replace("exact True.intro", "trivial", StringComparison.Ordinal),
            StatementMaterial = "new elaborated theorem",
        };
        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")], candidateModules: [candidate, Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData("Group.value?", "Outer.Mid.Group.value?", false)]
    [InlineData("Group.value?", "Outer.Mid.Group.value?", true)]
    [InlineData("_root_.globalValue!", "globalValue!", false)]
    [InlineData("_root_.globalValue!", "globalValue!", true)]
    public void MathlibReanchorResolvesQualifiedDefinitionBodies(
        string sourceName, string recordedName, bool mutate)
    {
        var source = $"namespace Outer\nnamespace Mid\ndef {sourceName} : Nat := 1\nend Mid\nend Outer\n";
        var baseline = ModuleWithReport("A", source, "old elaborated definition",
            declarations: [recordedName], kind: "def");
        var candidate = baseline with
        {
            Source = mutate ? source.Replace(":= 1", ":= 2", StringComparison.Ordinal) : source,
            StatementMaterial = "new elaborated definition",
        };
        var result = ValidateMathlibReanchor(
            baseModules: [baseline, Module("B")], candidateModules: [candidate, Module("B")],
            replacedModules: ["A"], environment: ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }
}
