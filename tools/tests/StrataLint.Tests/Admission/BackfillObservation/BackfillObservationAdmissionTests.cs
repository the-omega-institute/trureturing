using System.Runtime.InteropServices;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string ObservedTheoryPath = "docs/develop/theory/OBSERVED_VOLUME.md";
    private const string ObservedTheoryFinding =
        "theory document 'docs/develop/theory/OBSERVED_VOLUME.md' has no digestion source: "
        + "run make ingest, which registers it with the default atomizer";

    [Fact]
    public void CoverAtomObserveFindingDoesNotBlockAndIsPrinted()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec());
        materialized.Files[ObservedTheoryPath] = "# Observed volume\n";
        materialized.Baseline[ObservedTheoryPath] = "# Observed volume\n";
        var inputs = DirectoryInputs(materialized);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["cover-atom", .. CoverArgs(inputs)],
            BuildCoverEnvironment(temporary.Path, inputs, inputs.Files),
            console);

        Assert.Equal(0, exitCode);
        Assert.Empty(console.Error);
        Assert.Contains("COVER atom_id=", console.Output, StringComparison.Ordinal);
        Assert.Contains("OBSERVED SL-016 Meta/BACKFILL.yaml: " + ObservedTheoryFinding,
            console.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestObserveFindingDoesNotBlockAndIsPrinted()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var prefix = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。claim。\n\n# Notes\n");
        var appendedClaim = Encoding.UTF8.GetBytes("\n**定理 1.2(B)**。observed。\n");
        var sourceBytes = prefix.Concat(Enumerable.Repeat((byte)' ', appendedClaim.Length)).ToArray();
        var changedSourceBytes = prefix.Concat(appendedClaim).ToArray();
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var changedAtoms = AtomizerRegistry.Atomize(
            atomizerId,
            changedSourceBytes,
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(
            atom.Fingerprints,
            Assert.Single(changedAtoms, candidate => candidate.Fingerprints.RawSha256 == atom.Fingerprints.RawSha256).Fingerprints);
        var observedAtom = Assert.Single(changedAtoms, candidate => candidate.Fingerprints.RawSha256 != atom.Fingerprints.RawSha256);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var emptyBaseline = DigestionTestSupport.Document(
            atomizerId,
            [],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, emptyBaseline);
        // Drop the atom's CAS object from the baseline by prefix rather than by
        // reconstructing its content address. Capture(...).RelativePath would embed a
        // runtime-computed hash in the path, which ScribeTestMapDeriver cannot resolve
        // statically; that makes the method a conservative unknown and SL-003 blocks any
        // such method introduced after the fork point. Matching on the store root keeps
        // every path this test touches a string literal.
        foreach (var casPath in fixture.Baseline.Keys
            .Where(static path => path.StartsWith("Meta/Digestion/atoms/sha256/", StringComparison.Ordinal))
            .ToArray())
        {
            fixture.Baseline.Remove(casPath);
        }
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var current = Snapshot(fixture.Files);
        var currentSource = current.Entries.Single(entry =>
            entry.Path == RuleFixture.FixtureDigestionSourcePath);
        // Load runs after DigestionIngestor.Plan. An equal-length byte replacement makes the
        // final validation see one residual that the plan could not have registered.
        var mutableSourceBytes = ImmutableCollectionsMarshal.AsArray(currentSource.Bytes)!;
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                current,
                Snapshot(fixture.Baseline)),
            new MutatingLeanReportSource(
                LeanAxiomReport.Create(fixture.Reports),
                // Array.Copy rather than changedSourceBytes.CopyTo(...): ScribeTestMapDeriver
                // matches file-reading APIs by method name alone, so an array CopyTo is taken
                // for a file copy, its first argument fails the literal-path test, and the
                // whole method becomes a conservative unknown that SL-003 blocks. Same bytes,
                // same semantics, no false positive.
                () => Array.Copy(changedSourceBytes, mutableSourceBytes, changedSourceBytes.Length)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-digestion-status", "--base", "baseline"],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Empty(console.Error);
        Assert.Contains("INGEST stale_acknowledged=", console.Output, StringComparison.Ordinal);
        Assert.Single(console.Output.Split('\n'), static line =>
            line.StartsWith("OBSERVED ", StringComparison.Ordinal));
        Assert.Contains(
            "OBSERVED SL-016 Meta/BACKFILL.yaml: source fixture-source "
            + $"has unregistered residual-open atom {AtomId(observedAtom)}",
            console.Output,
            StringComparison.Ordinal);
        Assert.Contains("run make ingest to close it", console.Output, StringComparison.Ordinal);
    }
}

internal sealed class MutatingLeanReportSource(LeanAxiomReport report, Action mutation) : ILeanReportSource
{
    public LeanAxiomReport Load(RepositorySnapshot snapshot)
    {
        mutation();
        return report;
    }
}
