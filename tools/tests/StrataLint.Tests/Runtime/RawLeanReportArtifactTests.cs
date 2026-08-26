using System.Text;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RawLeanReportArtifactTests
{
    private const string Source = "axiom probe : False\n";

    private const string CanonicalReport =
        "{\"modules\": [{\"declarations\": [{\"axioms\": [], \"include_in_statement\": true, "
        + "\"kind\": \"axiom\", \"name\": \"probe\", \"name_key\": \"ns(n0,5:probe)\", "
        + "\"type\": \"statement-v1(test)\"}], \"imports\": [], \"module\": \"Trureturing\", "
        + "\"source_path\": \"Trureturing.lean\", \"source_sha256\": "
        + "\"sha256:da33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4\"}], "
        + "\"schema\": \"stratalint-raw-lean-report-v1\"}\n";

    [Fact]
    public void CanonicalReportFeedsLeanFileReportAndTheExistingStatementWriter()
    {
        var snapshot = Snapshot();

        var report = RawLeanReportArtifact.Read(
            Encoding.UTF8.GetBytes(CanonicalReport),
            snapshot);

        Assert.True(RepoPath.TryCreate("Trureturing.lean", out var path));
        var file = Assert.Single(report.Files).Value;
        var declaration = Assert.Single(file.Declarations);
        Assert.Equal("probe", declaration.Name);
        Assert.Equal("statement-v1(test)", declaration.TypeRepresentation);
        var statement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(path, file));
        Assert.StartsWith("sha256:", statement.StatementId.Value, StringComparison.Ordinal);
    }

    [Fact]
    public void WriterIsByteStableAndUsesTheStructuredCanonicalJsonShape()
    {
        var snapshot = Snapshot();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["Trureturing.lean"] = new(
                [],
                [new LeanDeclaration("probe", "axiom", "statement-v1(test)", [])
                {
                    NameKey = "ns(n0,5:probe)",
                }]),
        });

        var first = RawLeanReportArtifact.Write(snapshot, report);
        var second = RawLeanReportArtifact.Write(snapshot, report);

        var actual = Encoding.UTF8.GetString(first.AsSpan());
        Assert.True(
            string.Equals(CanonicalReport, actual, StringComparison.Ordinal),
            $"expected:\n{CanonicalReport}\nactual:\n{actual}");
        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.Matches("^sha256:[0-9a-f]{64}$", RawLeanReportArtifact.ContentAddress(first.AsSpan()));
    }

    [Fact]
    public void ReaderRejectsSemanticallyValidButNoncanonicalJsonBytes()
    {
        var noncanonical = CanonicalReport.Replace(": ", ":", StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(noncanonical), Snapshot()));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsAReportWhoseSourceHashDoesNotMatchTheSnapshot()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", "axiom changed : False\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(CanonicalReport), snapshot));

        Assert.Contains("source hash", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsAPoisonedCachedModuleWhoseKeyWasIncorrectlyReused()
    {
        var poisoned = CanonicalReport.Replace(
            "da33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4",
            "0a33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(poisoned), Snapshot()));

        Assert.Contains("source hash", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsACachedReportMissingAManagedModule()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", Source),
            RawRepositoryEntry.FromText("D5/Extra.lean", "def extra : Nat := 1\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(CanonicalReport), snapshot));

        Assert.Contains("module", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void StandaloneLeanInspectorWritesAConsumerAcceptedArtifact()
    {
        const string unicodeSource = "def term𝒪φ : Nat := 1\n";
        using var repository = new TemporaryDirectory();
        File.WriteAllText(
            Path.Combine(repository.Path, "lakefile.toml"),
            "name = \"producer_probe\"\nversion = \"0.1.0\"\ndefaultTargets = [\"Trureturing\"]\n\n[[lean_lib]]\nname = \"Trureturing\"\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "lean-toolchain"),
            "leanprover/lean4:v4.31.0\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "Trureturing.lean"),
            unicodeSource,
            new UTF8Encoding(false));
        var build = TestProcessRunner.Run(
            "lake",
            ["build"],
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            8 * 1024 * 1024);
        Assert.True(
            build.ExitCode == 0,
            Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));
        var output = Path.Combine(repository.Path, "raw-lean-report.json");
        var inspector = Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "lean-inspector",
            "Inspector.lean");
        var sourceHash = "sha256:" + Convert.ToHexStringLower(
            SHA256.HashData(Encoding.UTF8.GetBytes(unicodeSource)));

        var inspected = TestProcessRunner.Run(
            "lake",
            [
                "env", "lean", "--run", inspector,
                "--output", output,
                "Trureturing", "Trureturing.lean", sourceHash,
            ],
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            8 * 1024 * 1024);

        Assert.True(
            inspected.ExitCode == 0,
            Encoding.UTF8.GetString(inspected.StandardOutput)
                + Encoding.UTF8.GetString(inspected.StandardError));
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", unicodeSource),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = RawLeanReportArtifact.ReadFile(output, snapshot);
        Assert.Contains(
            report.Files.Single().Value.Declarations,
            declaration => declaration.Name == "term𝒪φ");
    }

    private static RepositorySnapshot Snapshot()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", Source),
        });
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

}
