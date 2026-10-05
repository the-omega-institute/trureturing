using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Fact]
    public void CoverReadsItsScopeAndTheDeclaredPathsAndNoRevisionOrChangeSet()
    {
        const string unrelated = "docs/reports/unrelated.json";
        var inputs = new CoverSpec().Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        currentFiles[unrelated] = "{}\n";
        baselineFiles[unrelated] = "{}\n";
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            CoverWorld.Raw(currentFiles),
            CoverWorld.Raw(baselineFiles));

        var result = CoverAtomCommand.Run(
            temporary.Path,
            repository,
            new FakeLeanReportSource(inputs.Report),
            CoverWorld.FixtureUtc,
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, repository.WholeTreeReadCount);
        Assert.Equal(2, repository.ScopedCurrentReads.Count);
        Assert.Equal(["Meta", "D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"], repository.ScopedCurrentReads[0]);
        Assert.Contains(repository.ScopedCurrentReads[1], spec => spec.StartsWith(":(literal)docs/", StringComparison.Ordinal));
        Assert.All(repository.ScopedCurrentReads.SelectMany(static scope => scope),
            static spec => Assert.DoesNotContain("docs/reports", spec, StringComparison.Ordinal));
        Assert.Empty(repository.ReadRevisionCalls);
        Assert.Empty(repository.ReadChangesCalls);
    }

    [Fact]
    public void ScopedReadsReturnOnlyTheRequestedPaths()
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/domains.yaml"] = "domains\n",
            ["Meta/Digestion/atomizers.toml"] = "rules\n",
            ["D5/S0/Carrier/Probe.lean"] = "theorem probe : True := True.intro\n",
            ["D5.lean"] = "sibling of the D5 directory\n",
            ["docs/source.md"] = "source\n",
            ["docs/reports/unrelated.json"] = "{}\n",
        };
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()), CoverWorld.Raw(files), CoverWorld.Raw(files));

        var current = repository.ReadCurrent(["Meta", "D5", ":(literal)docs/source.md"]);
        var baseline = repository.ReadRevision("baseline", ["D5", "docs/source.md"]);

        Assert.Equal(
            ["D5/S0/Carrier/Probe.lean", "Meta/Digestion/atomizers.toml", "Meta/domains.yaml", "docs/source.md"],
            current.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal).ToArray());
        Assert.Equal(
            ["D5/S0/Carrier/Probe.lean", "docs/source.md"],
            baseline.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal).ToArray());
        Assert.Throws<ArgumentException>(() => repository.ReadCurrent([]));
        Assert.Throws<ArgumentException>(() => repository.ReadRevision("baseline", []));
    }
}
