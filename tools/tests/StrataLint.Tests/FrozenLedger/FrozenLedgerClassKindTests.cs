using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("", "Type")]
    [InlineData("", "Prop")]
    [InlineData("@[ext] ", "Type")]
    public void MathlibReanchorRecognizesClassAsCompiledInductive(string prefix, string sort)
    {
        var source = $"namespace N\n{prefix}class C : {sort} where\n  witness : True\nend N\n";
        var baseline = ModuleWithReport("A", source, "old elaborated class", kind: "inductive", declarations: ["N.C"]);
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")],
            [baseline with { StatementMaterial = "new elaborated class" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("class C where\n  value : Nat\n", "class C where\n  value : Bool\n")]
    [InlineData("class C : Prop where\n  witness : True\n", "class C : Prop where\n  witness : False\n")]
    [InlineData("class C (n : Nat) where\n  value : Fin n\n", "class C (n : Nat) where\n  value : Fin (n + 1)\n")]
    public void MathlibReanchorRejectsChangedClassContent(string before, string after)
    {
        var baseline = ModuleWithReport("A", before, "old elaborated class", kind: "inductive", declarations: ["C"]);
        var candidate = baseline with { Source = after, StatementMaterial = "new elaborated class" };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesClassDependenciesOfTheorem(bool mutate)
    {
        var source = "class C : Prop where\n  witness : True\ntheorem a [C] : True := by exact True.intro\n";
        var baseline = ModuleWithReport("A", source, "old theorem");
        var candidate = baseline with
        {
            Source = source.Replace("exact True.intro", "trivial", StringComparison.Ordinal)
                .Replace("witness : True", mutate ? "witness : False" : "witness : True", StringComparison.Ordinal),
            StatementMaterial = "new theorem",
        };
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [candidate, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData("def")]
    [InlineData("theorem")]
    [InlineData("constructor")]
    [InlineData("recursor")]
    public void MathlibReanchorRejectsClassRecordedAsDifferentKind(string kind)
    {
        var baseline = ModuleWithReport("A", "class C where\n  value : Nat\n", "old class", kind: kind, declarations: ["C"]);
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [baseline with { StatementMaterial = "new class" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData("def C : Nat := 1\n")]
    [InlineData("theorem C : True := by trivial\n")]
    public void MathlibReanchorRejectsNonClassRecordedAsInductive(string source)
    {
        var baseline = ModuleWithReport("A", source, "old material", kind: "inductive", declarations: ["C"]);
        var result = ValidateMathlibReanchor(
            [baseline, Module("B")], [baseline with { StatementMaterial = "new material" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
