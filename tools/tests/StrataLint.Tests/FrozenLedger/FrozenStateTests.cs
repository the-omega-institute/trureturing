using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenStateTests
{
    private const string ModulePath = "D5/S0/Carrier/Ring.lean";
    private const string StatePath = "Golden/Frozen/state/D5/S0/Carrier/Ring.lean.json";
    private const string Pin =
        "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    [Theory]
    [InlineData(ModulePath, StatePath)]
    [InlineData("Trureturing.lean", "Golden/Frozen/state/Trureturing.lean.json")]
    public void StatePathAndModulePathAreExactInverses(string modulePath, string statePath)
    {
        var module = RepoPath.CreateKnown(modulePath);

        var state = FrozenStatePath.FromModulePath(module);

        Assert.Equal(statePath, state.Value);
        Assert.True(FrozenStatePath.TryToModulePath(state.Value, out var decoded));
        Assert.Equal(module, decoded);
    }

    [Theory]
    [InlineData("Golden/Frozen/state/D5/S0/Carrier/../Ring.lean.json")]
    [InlineData("Golden/Frozen/state/D5/S0/Carrier/Ring.json")]
    [InlineData("Golden/Frozen/state/d5/S0/Carrier/Ring.lean.json")]
    [InlineData("Golden/Frozen/other/D5/S0/Carrier/Ring.lean.json")]
    public void StatePathRejectsNonCanonicalAddresses(string path) =>
        Assert.False(FrozenStatePath.TryToModulePath(path, out _));

    public static TheoryData<string> InvalidRecords => new()
    {
        { $"{{\"statement_id\":\"{Pin}\",\"event_hash\":\"{Pin}\"}}\n" },
        { "{}\n" },
        { "{\"statement_id\":\"sha256:ABC\"}\n" },
        { $"{{\"statement_id\":\"{Pin}\"}}\n{{}}\n" },
        { $"\uFEFF{{\"statement_id\":\"{Pin}\"}}\n" },
    };

    [Theory]
    [MemberData(nameof(InvalidRecords))]
    public void StrictLoaderRejectsMalformedRecordsAndNamesThePath(string text)
    {
        var file = RepositoryStateFile(StatePath, Encoding.UTF8.GetBytes(text));

        var exception = Assert.Throws<FormatException>(() => FrozenStateRecordLoader.Load(file));

        Assert.Contains(StatePath, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CatalogLoadsSelectorToPinAndRejectsIllegalPathsUnderTheRoot()
    {
        var valid = RepositoryStateFile(StatePath, Encoding.UTF8.GetBytes($"{{\"statement_id\":\"{Pin}\"}}\n"));
        const string rootStatePath = "Golden/Frozen/state/Trureturing.lean.json";
        var root = RepositoryStateFile(
            rootStatePath,
            Encoding.UTF8.GetBytes($"{{\"statement_id\":\"{Pin}\"}}\n"));
        var catalog = FrozenStateCatalog.Load(Snapshot(valid, root));

        Assert.Equal(2, catalog.Records.Count);
        Assert.Equal(Pin, catalog.Records[RepoPath.CreateKnown(ModulePath)].StatementId.Value);
        Assert.Equal(Pin, catalog.Records[RepoPath.CreateKnown("Trureturing.lean")].StatementId.Value);

        const string invalidPath = "Golden/Frozen/state/not-a-module.json";
        var invalid = RepositoryStateFile(invalidPath, Encoding.UTF8.GetBytes($"{{\"statement_id\":\"{Pin}\"}}\n"));
        var exception = Assert.Throws<FormatException>(() => FrozenStateCatalog.Load(Snapshot(invalid)));
        Assert.Contains(invalidPath, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WriterIsByteStableAndReturnsFalseForAnIdenticalSecondWrite()
    {
        using var temporary = new TemporaryDirectory();
        var module = RepoPath.CreateKnown(ModulePath);
        var statement = StatementId.Create(Pin);

        Assert.True(FrozenStateWriter.Write(temporary.Path, module, statement));
        var absolute = Path.Combine(temporary.Path, StatePath.Replace('/', Path.DirectorySeparatorChar));
        var first = File.ReadAllBytes(absolute);
        Assert.Equal($"{{\"statement_id\":\"{Pin}\"}}\n", Encoding.UTF8.GetString(first));

        Assert.False(FrozenStateWriter.Write(temporary.Path, module, statement));
        Assert.Equal(first, File.ReadAllBytes(absolute));
    }

    private static RepositoryFile RepositoryStateFile(string path, byte[] bytes) =>
        new(
            RepoPath.CreateKnown(path),
            ImmutableArray.CreateRange(bytes),
            Encoding.UTF8.GetString(bytes));

    private static RepositorySnapshot Snapshot(params RepositoryFile[] files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path));
}
