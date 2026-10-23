using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void MathlibReanchorResolvesImportedGeneratedDefinitionOwner(bool decoy, bool mutate)
    {
        var source = "import D5.S0.Carrier.B\n"
            + (decoy ? "def value : Prop := True\n" : "")
            + "theorem a : True := by trivial\n";
        var root = ModuleWithReport("A", source, "old generated theorem",
            declarations: ["Owner.value.eq_def"]) with { Imports = ["B"] };
        var owner = ModuleWithReport("B", "namespace Owner\ndef value : Prop := True\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, owner], [root with { StatementMaterial = "new generated theorem" },
                owner with { Source = mutate ? owner.Source.Replace("True", "False", StringComparison.Ordinal) : owner.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesImportedOwnerTransitiveDefinitionDependency(bool mutate)
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.C\ntheorem a : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]) with { Imports = ["C"] };
        var middle = Module("C", "import D5.S0.Carrier.B\ntheorem c : True := by trivial\n", imports: ["B"]);
        var owner = ModuleWithReport("B", "namespace Owner\ndef premise : Prop := True\ndef value : Prop := premise\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, middle, owner], [root with { StatementMaterial = "new generated theorem" }, middle,
                owner with { Source = mutate ? owner.Source.Replace(":= True", ":= False", StringComparison.Ordinal) : owner.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesImportedOwnerAmbientCommands(bool mutate)
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]) with { Imports = ["B"] };
        var owner = ModuleWithReport("B", "set_option autoImplicit false\nnamespace Owner\ndef value : Nat := 1\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, owner], [root with { StatementMaterial = "new generated theorem" },
                owner with { Source = mutate ? owner.Source.Replace("autoImplicit false", "autoImplicit true", StringComparison.Ordinal) : owner.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData("Owner.value.eq_def")]
    [InlineData("Owner.missing.eq_def")]
    [InlineData("List.range.loop.eq_def")]
    public void MathlibReanchorRejectsGeneratedNameWithoutImportedOwner(string name)
    {
        var root = ModuleWithReport("A", "theorem a : True := by trivial\n",
            "old generated theorem", declarations: [name]);
        var unimported = ModuleWithReport("B", "namespace Owner\ndef value : Nat := 1\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, unimported], [root with { StatementMaterial = "new generated theorem" }, unimported],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesImportedGeneratedRootAmbient(bool mutate)
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]) with { Imports = ["B"] };
        var owner = ModuleWithReport("B", "namespace Owner\ndef value : Nat := 1\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, owner], [root with
            {
                StatementMaterial = "new generated theorem",
                Source = mutate ? "import Mathlib.Data.Nat.Basic\n" + root.Source : root.Source,
            }, owner], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Theory]
    [InlineData("Owner.value.eq_def", "value")]
    [InlineData("List.range.loop.eq_def", "loop")]
    [InlineData("List.range.loop.eq_def", "range")]
    [InlineData("List.range.loop.eq_def", "range.loop")]
    public void MathlibReanchorRejectsImportedLeafDecoyForMissingOwner(string recorded, string decoy)
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n",
            "old generated theorem", declarations: [recorded]) with { Imports = ["B"] };
        var unrelated = ModuleWithReport("B", $"def {decoy} : Nat := 1\n",
            "stable unrelated definition", declarations: [decoy], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, unrelated], [root with { StatementMaterial = "new generated theorem" }, unrelated],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsImportedQuotedNameSegmentCollision()
    {
        var raw = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText(PathFor("A"), "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n"),
            RawRepositoryEntry.FromText(PathFor("B"), "namespace Owner\ndef value : Nat := 1\nend Owner\n"),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var sources = LeanSourceCatalog.Parse(snapshot);
        Assert.Throws<LeanSourceExtractionException>(() => sources.ExtractPropositionSource(
            RepoPathFor("A"), [new FrozenDeclaration("ns(ns(n0,11:Owner.value),6:eq_def)", "theorem")]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesExactImportedOwnerDespiteLongerLocalSuffix(bool mutate)
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem value.eq_def : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]) with { Imports = ["B"] };
        var owner = ModuleWithReport("B", "namespace Owner\ndef value : Nat := 1\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var result = ValidateMathlibReanchor(
            [root, owner], [root with { StatementMaterial = "new generated theorem" },
                owner with { Source = mutate ? owner.Source.Replace(":= 1", ":= 2", StringComparison.Ordinal) : owner.Source }],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!mutate, result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsMissingEquationOwnerDespiteLocalSuffix()
    {
        var root = ModuleWithReport("A", "theorem value.eq_def : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]);
        var result = ValidateMathlibReanchor(
            [root, Module("B")], [root with { StatementMaterial = "new generated theorem" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }

    [Fact]
    public void MathlibReanchorRejectsAmbiguousImportedGeneratedOwner()
    {
        var root = ModuleWithReport("A", "import D5.S0.Carrier.B\nimport D5.S0.Carrier.C\ntheorem a : True := by trivial\n",
            "old generated theorem", declarations: ["Owner.value.eq_def"]) with { Imports = ["B", "C"] };
        var owner = ModuleWithReport("B", "namespace Owner\ndef value : Nat := 1\nend Owner\n",
            "stable definition", declarations: ["Owner.value"], kind: "def");
        var duplicate = owner with { Name = "C" };
        var result = ValidateMathlibReanchor(
            [root, owner, duplicate], [root with { StatementMaterial = "new generated theorem" }, owner, duplicate],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
