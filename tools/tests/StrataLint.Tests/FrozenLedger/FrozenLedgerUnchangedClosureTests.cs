using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("_f", false)]
    [InlineData("_f", true)]
    [InlineData("_unsafe_rec", false)]
    [InlineData("_sunfold", true)]
    [InlineData("match_1.splitter", true)]
    [InlineData("_aux_1", true)]
    public void MathlibReanchorUnchangedClosurePreservesGeneratedRoots(string suffix, bool imported)
    {
        const string owner = "namespace Owner\nprivate def value : Nat := 1\nend Owner\n";
        var module = imported ? "B" : "A";
        var key = PrivateEquationKey("D5.S0.Carrier." + module, suffix: "." + suffix);
        var sources = ClosureSources(imported ? owner : null, localOwner: imported ? null : owner);
        Assert.True(CompleteClosureEqual(sources, sources, [new(key, "def")], [new(key, "def")]));
    }

    [Theory]
    [InlineData("private def value : Nat := 1\n", "private def value : Nat := 2\n")]
    [InlineData("private def value : Nat := 1\nprivate theorem value._f : True := by trivial\n",
        "private def value : Nat := 1\nprivate theorem value._f : True ∧ True := by constructor <;> trivial\n")]
    [InlineData("private def value : Nat := 1\ndef value._f : Nat := 2\n",
        "private def value : Nat := 1\ndef value._f : Nat := 3\n")]
    [InlineData("inductive Flag | left | right\nprivate def value : Nat := Flag.ctorIdx Flag.left\n",
        "inductive Flag | right | left\nprivate def value : Nat := Flag.ctorIdx Flag.left\n")]
    [InlineData("private def value : Nat := 1\ntheorem generate : True := by run_tac Lean.addDecl (.defnDecl { name := `made, levelParams := [], type := Lean.mkConst ``Nat, value := Lean.mkNatLit 7, hints := .opaque, safety := .safe }); trivial\n",
        "private def value : Nat := 1\ntheorem generate : True := by run_tac Lean.addDecl (.defnDecl { name := `made, levelParams := [], type := Lean.mkConst ``Nat, value := Lean.mkNatLit 8, hints := .opaque, safety := .safe }); trivial\n")]
    public void MathlibReanchorUnchangedClosureRejectsChangedGeneratorSources(string before, string after)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        var original = ClosureSources(before);
        var changed = ClosureSources(after);
        Assert.True(CompleteClosureEqual(original, original, [new(key, "def")], [new(key, "def")]));
        Assert.False(CompleteClosureEqual(original, changed, [new(key, "def")], [new(key, "def")]));
    }

    [Theory]
    [InlineData("def c : Nat := 1\n", "def c : Nat := 2\n")]
    [InlineData("theorem c : True := by trivial\n", "theorem c : True := by exact True.intro\n")]
    [InlineData("inductive Flag | left | right\n", "inductive Flag | right | left\n")]
    [InlineData("run_cmd Lean.logInfo \"before\"\n", "run_cmd Lean.logInfo \"after\"\n")]
    [InlineData("set_option autoImplicit false\n", "set_option autoImplicit true\n")]
    [InlineData("macro \"magic\" : term => `(1)\n", "macro \"magic\" : term => `(2)\n")]
    public void MathlibReanchorUnchangedClosureKeepsEveryTransitiveImportByte(string before, string after)
    {
        const string owner = "import D5.S0.Carrier.C\nnamespace Owner\nprivate def value : Nat := 1\nend Owner\n";
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        var original = ClosureSources(owner, before);
        Assert.True(CompleteClosureEqual(original, original, [new(key, "def")], [new(key, "def")]));
        Assert.False(CompleteClosureEqual(original, ClosureSources(owner, after), [new(key, "def")], [new(key, "def")]));
    }

    [Theory]
    [InlineData("kind")]
    [InlineData("name")]
    [InlineData("duplicate")]
    [InlineData("removed")]
    public void MathlibReanchorUnchangedClosureKeepsEntireRootInventory(string mutation)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        var source = ClosureSources("namespace Owner\nprivate def value : Nat := 1\nend Owner\n");
        ImmutableArray<FrozenDeclaration> original = [new(key, "def")];
        ImmutableArray<FrozenDeclaration> changed = mutation switch
        {
            "kind" => [new(key, "theorem")],
            "name" => [new(PrivateEquationKey("D5.S0.Carrier.B", suffix: "._unsafe_rec"), "def")],
            "duplicate" => [new(key, "def"), new(key, "def")],
            _ => [],
        };
        Assert.False(CompleteClosureEqual(source, source, original, changed));
    }

    [Fact]
    public void MathlibReanchorUnchangedClosureRejectsMissingManagedImport()
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        var source = ClosureSources("import D5.S0.Carrier.C\nprivate def value : Nat := 1\n");
        Assert.False(CompleteClosureEqual(source, source, [new(key, "def")], [new(key, "def")]));
    }

    [Fact]
    public void MathlibReanchorUnchangedClosureDoesNotRequireUnrelatedSourceEquality()
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        const string owner = "namespace Owner\nprivate def value : Nat := 1\nend Owner\n";
        Assert.True(CompleteClosureEqual(ClosureSources(owner, "def c : Nat := 1\n"),
            ClosureSources(owner, "def c : Nat := 2\n"), [new(key, "def")], [new(key, "def")]));
    }

    [Theory]
    [InlineData("D5.S0.Carrier.C", 0, true, false)]
    [InlineData("D5.S0.Carrier.B", 1, true, false)]
    [InlineData("D5.S0.Carrier.B", 0, false, false)]
    [InlineData("D5.S0.Carrier.B", 0, true, true)]
    public void MathlibReanchorUnchangedClosureRejectsInvalidPrivateModulePrefix(
        string module, int index, bool numeric, bool quoted)
    {
        var key = PrivateEquationKey(module, index, numeric, quotedModule: quoted, suffix: "._f");
        var sources = ClosureSources("namespace Owner\nprivate def value : Nat := 1\nend Owner\n",
            "private def value : Nat := 1\n");
        Assert.False(CompleteClosureEqual(sources, sources, [new(key, "def")], [new(key, "def")]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorUnchangedClosureStillValidatesExplicitRoots(bool privateFirst)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: "._f");
        var sources = ClosureSources("namespace Owner\nprivate def value : Nat := 1\nend Owner\n");
        ImmutableArray<FrozenDeclaration> roots = privateFirst
            ? [new(key, "def"), new("ns(n0,1:a)", "def")]
            : [new("ns(n0,1:a)", "def"), new(key, "def")];
        Assert.False(CompleteClosureEqual(sources, sources, roots, roots));
    }

    private static RepositorySnapshot ClosureSources(string? owner, string? leaf = null, string? localOwner = null)
    {
        var root = owner is null ? localOwner + "theorem a : True := by trivial\n"
            : "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n";
        var entries = new List<RawRepositoryEntry> { RawRepositoryEntry.FromText(PathFor("A"), root) };
        if (owner is not null) entries.Add(RawRepositoryEntry.FromText(PathFor("B"), owner));
        if (leaf is not null) entries.Add(RawRepositoryEntry.FromText(PathFor("C"), leaf));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
    }

    private static bool CompleteClosureEqual(RepositorySnapshot before, RepositorySnapshot after,
        ImmutableArray<FrozenDeclaration> oldRoots, ImmutableArray<FrozenDeclaration> newRoots)
    {
        try
        {
            var sources = LeanPropositionSourceComparer.ParseSources(before, after);
            var left = sources.Base.ExtractPropositionSource(RepoPathFor("A"), oldRoots);
            var right = sources.Candidate.ExtractPropositionSource(RepoPathFor("A"), newRoots);
            return left.AsSpan().SequenceEqual(right.AsSpan());
        }
        catch (LeanSourceExtractionException) { return false; }
    }
}
