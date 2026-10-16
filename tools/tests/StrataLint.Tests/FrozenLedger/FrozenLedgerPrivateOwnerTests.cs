using System.Collections.Immutable;
using System.Text;
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
    public void MathlibReanchorResolvesExactPrivateEquationOwner(bool imported, bool mutate)
    {
        var key = PrivateEquationKey(imported ? "D5.S0.Carrier.B" : "D5.S0.Carrier.A");
        var source = "namespace Owner\nprivate def value : Nat := 1\nend Owner\n";
        var before = ExtractPrivateEquation(imported, source, key);
        var after = ExtractPrivateEquation(imported,
            mutate ? source.Replace(":= 1", ":= 2", StringComparison.Ordinal) : source, key);
        Assert.Equal(!mutate, before.AsSpan().SequenceEqual(after.AsSpan()));
    }

    [Theory]
    [InlineData(false, "def")]
    [InlineData(true, "def")]
    [InlineData(true, "public def")]
    [InlineData(true, "@[simp] def")]
    public void MathlibReanchorRejectsPublicDecoyForPrivateEquationOwner(bool imported, string modifiers)
    {
        var key = PrivateEquationKey(imported ? "D5.S0.Carrier.B" : "D5.S0.Carrier.A");
        Assert.Throws<LeanSourceExtractionException>(() => ExtractPrivateEquation(imported,
            $"namespace Owner\n{modifiers} value : Nat := 1\nend Owner\n", key));
    }

    [Theory]
    [InlineData(false, "")]
    [InlineData(true, "")]
    [InlineData(false, ".match_1")]
    [InlineData(true, ".match_1")]
    public void MathlibReanchorRejectsPrivateRecordedNameSubstringFallback(bool imported, string suffix)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", suffix: suffix);
        Assert.Throws<LeanSourceExtractionException>(() => ExtractPrivateEquation(imported,
            "namespace Owner\ndef value : Nat := 1\nend Owner\n", key, "def"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorResolvesExactPrivateDefinition(bool imported)
    {
        var key = PrivateEquationKey(imported ? "D5.S0.Carrier.B" : "D5.S0.Carrier.A", suffix: "");
        var before = ExtractPrivateEquation(imported,
            "namespace Owner\nprivate def value : Nat := 1\nend Owner\n", key, "def");
        var after = ExtractPrivateEquation(imported,
            "namespace Owner\nprivate def value : Nat := 2\nend Owner\n", key, "def");
        Assert.False(before.AsSpan().SequenceEqual(after.AsSpan()));
    }

    [Theory]
    [InlineData("value")]
    [InlineData("value.eq_def")]
    public void MathlibReanchorRejectsPrivateDeclarationKindMismatch(string name)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", name: "Owner." + name, suffix: "");
        Assert.Throws<LeanSourceExtractionException>(() => ExtractPrivateEquation(true,
            $"namespace Owner\nprivate def {name} : Nat := 1\nend Owner\n", key));
    }

    [Theory]
    [InlineData("@[simp] private def")]
    [InlineData("private noncomputable def")]
    [InlineData("@[simp] private noncomputable def")]
    public void MathlibReanchorResolvesPrivateModifierAfterAttributes(string modifiers)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B");
        var before = ExtractPrivateEquation(true,
            $"namespace Owner\n{modifiers} value : Nat := 1\nend Owner\n", key);
        var after = ExtractPrivateEquation(true,
            $"namespace Owner\n{modifiers} value : Nat := 2\nend Owner\n", key);
        Assert.False(before.AsSpan().SequenceEqual(after.AsSpan()));
    }

    [Theory]
    [InlineData("D5.S0.Carrier.A", 0, true, "Owner.value")]
    [InlineData("D5.S0.Carrier.C", 0, true, "Owner.value")]
    [InlineData("D5.S0.Carrier", 0, true, "Owner.value")]
    [InlineData("D5.S0.Carrier.B", 1, true, "Owner.value")]
    [InlineData("D5.S0.Carrier.B", 0, false, "Owner.value")]
    [InlineData("D5.S0.Carrier.B", 0, true, "Owner.missing")]
    public void MathlibReanchorRejectsPrivateEquationWithoutExactPrefixOwner(
        string module, int index, bool numeric, string name)
    {
        var key = PrivateEquationKey(module, index, numeric, name);
        Assert.Throws<LeanSourceExtractionException>(() => ExtractPrivateEquation(true,
            "namespace Owner\nprivate def value : Nat := 1\nend Owner\n", key));
    }

    [Fact]
    public void MathlibReanchorRejectsQuotedPrivateModuleSegmentCollision()
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B", quotedModule: true);
        Assert.Throws<LeanSourceExtractionException>(() => ExtractPrivateEquation(true,
            "namespace Owner\nprivate def value : Nat := 1\nend Owner\n", key));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesPrivateOwnerDefinitionDependencies(bool mutate)
    {
        var key = PrivateEquationKey("D5.S0.Carrier.B");
        var source = "namespace Owner\ndef premise : Prop := True\nprivate def value : Prop := premise\nend Owner\n";
        var before = ExtractPrivateEquation(true, source, key);
        var after = ExtractPrivateEquation(true,
            mutate ? source.Replace(":= True", ":= False", StringComparison.Ordinal) : source, key);
        Assert.Equal(!mutate, before.AsSpan().SequenceEqual(after.AsSpan()));
    }

    private static ImmutableArray<byte> ExtractPrivateEquation(bool imported, string owner, string key, string kind = "theorem")
    {
        var root = imported
            ? "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n"
            : owner + "theorem a : True := by trivial\n";
        var entries = new List<RawRepositoryEntry> { RawRepositoryEntry.FromText(PathFor("A"), root) };
        if (imported) entries.Add(RawRepositoryEntry.FromText(PathFor("B"), owner));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
        return LeanSourceCatalog.Parse(snapshot).ExtractPropositionSource(
            RepoPathFor("A"), [new FrozenDeclaration(key, kind)]);
    }

    private static string PrivateEquationKey(string module, int index = 0, bool numeric = true,
        string name = "Owner.value", bool quotedModule = false, string suffix = ".eq_def")
    {
        static string Str(string parent, string value) => $"ns({parent},{Encoding.UTF8.GetByteCount(value)}:{value})";
        var key = Str("n0", "_private");
        foreach (var segment in quotedModule ? [module] : module.Split('.')) key = Str(key, segment);
        key = numeric ? $"nn({key},{index})" : Str(key, index.ToString(System.Globalization.CultureInfo.InvariantCulture));
        foreach (var segment in (name + suffix).Split('.')) key = Str(key, segment);
        return key;
    }
}
