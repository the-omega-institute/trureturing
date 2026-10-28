using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void MathlibReanchorAcceptsUnchangedIndentedSource()
    {
        var source = "  theorem a : True := by trivial\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old elaborated True")],
            [ModuleWithReport("A", source, "new elaborated True")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("False", "True")]
    [InlineData("by trivial", "by exact True.intro")]
    public void MathlibReanchorRejectsChangedIndentedSource(string before, string after)
    {
        var source = "  theorem a : False := by trivial\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type")],
            [ModuleWithReport("A", source.Replace(before, after, StringComparison.Ordinal), "new type")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesOrdinaryConsumerOfIndentedSource(bool editProof)
    {
        var source = "import D5.S0.Carrier.B\ntheorem a : b := by trivial\n";
        var dependency = ModuleWithReport("B", "  def b : Prop := True\n", "stable b",
            declarations: ["b"], kind: "def");
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type") with { Imports = ["B"] }, dependency],
            [ModuleWithReport("A", editProof ? source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal) : source,
                "new type") with { Imports = ["B"] }, dependency],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!editProof, result.Authorized);
    }

    [Theory]
    [InlineData("class Flag where\n  value : Nat\ninstance flag : Flag := ⟨0⟩\nattribute [instance] flag\n",
        "class Flag where\n  value : Nat\ninstance flag : Flag := ⟨0⟩\nattribute [-instance] flag\n")]
    [InlineData("theorem witness : ∃ n : Nat, n = 0 := ⟨0, rfl⟩\n",
        "theorem witness : ∃ n : Nat, n = 1 := ⟨1, rfl⟩\n")]
    [InlineData("run_cmd Lean.logInfo \"before\"\n", "run_cmd Lean.logInfo \"after\"\n")]
    [InlineData("initialize counter : IO.Ref Nat ← IO.mkRef 0\n", "initialize counter : IO.Ref Nat ← IO.mkRef 1\n")]
    [InlineData("#check Nat\n", "#check Unit\n")]
    [InlineData("macro \"magic\" : command => `(def d : Nat := 0)\n",
        "macro \"magic\" : command => `(def d : Nat := 1)\n")]
    public void MathlibReanchorRejectsAnyChangedSourceInCompleteImportClosure(string before, string after)
    {
        var root = "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n";
        var middle = Module("B", "import D5.S0.Carrier.C\n  theorem b : True := by trivial\n", imports: ["C"]);
        var leaf = Module("C", "import Lean\ntheorem c : True := by trivial\n" + before);
        var unchanged = ValidateMathlibReanchor(
            [ModuleWithReport("A", root, "old type") with { Imports = ["B"] }, middle, leaf],
            [ModuleWithReport("A", root, "new type") with { Imports = ["B"] }, middle, leaf],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(unchanged.Authorized);
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", root, "old type") with { Imports = ["B"] }, middle, leaf],
            [ModuleWithReport("A", root, "new type") with { Imports = ["B"] }, middle,
                leaf with { Source = "import Lean\ntheorem c : True := by trivial\n" + after }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorDoesNotEraseProofsInCompleteImportClosure()
    {
        var root = "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n";
        var middle = Module("B", "import D5.S0.Carrier.C\n  theorem b : True := by trivial\n", imports: ["C"]);
        var leaf = Module("C", "theorem c : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", root, "old type") with { Imports = ["B"] }, middle, leaf],
            [ModuleWithReport("A", root, "new type") with { Imports = ["B"] }, middle,
                leaf with { Source = "theorem c : True := by exact True.intro\n" }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorKeepsUnrelatedProofEditingAvailable()
    {
        var source = "theorem a : True := by trivial\n";
        var unrelated = Module("B", "  theorem b : True := by trivial\n");
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type"), unrelated],
            [ModuleWithReport("A", source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal), "new type"), unrelated],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("a", "def")]
    [InlineData("other", "theorem")]
    public void MathlibReanchorPreservesInventoryForUnchangedIndentedSource(string declaration, string kind)
    {
        var source = "  theorem a : True := by trivial\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type")],
            [ModuleWithReport("A", source, "new type", declarations: [declaration], kind: kind)],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsMissingManagedSourceInCompleteClosure()
    {
        var source = "import D5.S0.Carrier.Missing\n  theorem a : True := by trivial\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type")],
            [ModuleWithReport("A", source, "new type")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorDoesNotBroadenOtherSourceFailures()
    {
        var malformed = Module("B", "end\ntheorem b : True := by trivial\n");
        var source = "  theorem a : True := by trivial\n";
        var result = ValidateMathlibReanchor(
            [ModuleWithReport("A", source, "old type"), malformed],
            [ModuleWithReport("A", source, "new type"), malformed],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
