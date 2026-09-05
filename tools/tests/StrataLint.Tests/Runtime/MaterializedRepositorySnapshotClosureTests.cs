using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MaterializedRepositorySnapshotClosureTests
{
    [Fact]
    public void FilteredAndUnfilteredRepositoryFixturesProduceByteIdenticalCapabilities()
    {
        var repositoryRoot = StrataLint.TestSupport.TestRepositoryLayout.FindRoot();
        var snapshot = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            EnumerateDeclared(repositoryRoot, "Blueprint")
                .Concat(EnumerateDeclared(repositoryRoot, "Chronicle"))
                .Concat(EnumerateDeclared(repositoryRoot, "D5"))
                .Concat(EnumerateDeclared(repositoryRoot, "Evidence"))
                .Concat(EnumerateDeclared(repositoryRoot, "Golden"))
                .Concat(EnumerateDeclared(repositoryRoot, "Library"))
                .Concat(EnumerateDeclared(repositoryRoot, "Meta"))
                .Concat(EnumerateDeclared(repositoryRoot, "Papers"))
                .Concat(EnumerateDeclared(repositoryRoot, "Problems"))
                .Select(static file => new RawRepositoryEntry(
                    file.RelativePath,
                    ImmutableArray.CreateRange(File.ReadAllBytes(file.FullPath))))));
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(snapshot).Snapshot;
        var report = ReportForDocuments(
            DocumentDefinitions.All.Select(static definition => definition.Document));
        using var unfilteredFixture = MaterializedRepositorySnapshot.Create(
            decoded,
            static _ => true);
        var unfilteredError = new StringWriter();
        var unfiltered = ScribeEmitter.Verify(
            unfilteredFixture.Root,
            unfilteredError,
            report);
        Assert.NotNull(unfiltered);
        Assert.Equal(string.Empty, unfilteredError.ToString());

        var filtered = new ProductionScribeEmissionVerifier().Verify(
            decoded,
            report,
            RawChangeSet.Create([]));

        Assert.Equal(
            CapabilityBytes(unfiltered!, report),
            CapabilityBytes(filtered, report));
    }

    [Fact]
    public void OutsideReadClosureProbeIsNotMaterializedAndDoesNotChangeVerifiedScribeEmissions()
    {
        var retained = RawRepositoryEntry.FromText(
            "D5/S0/Carrier/Probe.lean",
            "theorem probe : True := by trivial\n");
        var baseline = Snapshot(retained);
        var withOutsideFiles = Snapshot(
            retained,
            RawRepositoryEntry.FromText("outside/read-closure-probe.txt", "outside\n"),
            RawRepositoryEntry.FromText(
                "tools/Generated/scribe-emissions.v1.json",
                "generated output must not be read\n"));

        var baselineCapability = VerifyVisibleInputs(baseline);
        var probedCapability = VerifyVisibleInputs(withOutsideFiles);

        Assert.Equal(CapabilityBytes(baselineCapability), CapabilityBytes(probedCapability));
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Carrier/Probe.scribe.cs", false)]
    [InlineData("Golden/Projection/statement-projection-pilot-v1.json", false)]
    [InlineData("Golden/Projection/statement-projection-expansion-v1.json", false)]
    [InlineData("Meta/BACKFILL.yaml", false)]
    [InlineData("Meta/Digestion/backfill/probe/source.toml", false)]
    [InlineData("D5/S0/Carrier/Probe.lean", false)]
    [InlineData("Library/notes/probe.md", false)]
    [InlineData("Problems/probe.md", false)]
    [InlineData("Golden/Frozen/state/S0/Carrier/Probe.lean.json", true)]
    public void MaterializesEveryReaderOwnedInputPartition(string expectedPath, bool withProblemPool)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(expectedPath, "reader input\n"),
        };
        if (withProblemPool)
        {
            entries.Add(RawRepositoryEntry.FromText("Problems/.keep", string.Empty));
        }

        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.True(File.Exists(FullPath(root, expectedPath)), expectedPath);
            return VerifiedScribeEmissions.Empty;
        });

        verifier.Verify(Snapshot(entries.ToArray()), EmptyReport(), RawChangeSet.Create([]));
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Carrier/Probe.md")]
    [InlineData("Evidence/D5/S0/Carrier/Probe.result.json")]
    [InlineData("Chronicle/2026/09/05-probe.md")]
    [InlineData("Papers/recipes/D5-P001.yaml")]
    [InlineData("Papers/frozen/D5-P001/manifest.sha256")]
    public void DynamicGidAddressTargetsRemainVisible(string expectedPath)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.True(File.Exists(FullPath(root, expectedPath)), expectedPath);
            return VerifiedScribeEmissions.Empty;
        });

        verifier.Verify(
            Snapshot(RawRepositoryEntry.FromText(expectedPath, "GID target\n")),
            EmptyReport(),
            RawChangeSet.Create([]));
    }

    [Fact]
    public void EmptyAndMissingReaderDirectoriesKeepTheirExistenceState()
    {
        VerifyDirectoryState(Snapshot(), expected: false);
        VerifyDirectoryState(
            Snapshot(
                RawRepositoryEntry.FromText("Library/empty/.keep", string.Empty),
                RawRepositoryEntry.FromText("Problems/.keep", string.Empty),
                RawRepositoryEntry.FromText(
                    "Meta/Digestion/backfill/empty/.keep",
                    string.Empty)),
            expected: true);
    }

    private static VerifiedScribeEmissions VerifyVisibleInputs(RepositorySnapshot snapshot)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            var retainedIsVisible = File.Exists(FullPath(root, "D5/S0/Carrier/Probe.lean"));
            var outsideProbeIsVisible = File.Exists(FullPath(
                root,
                "outside/read-closure-probe.txt"));
            var generatedEmissionIsVisible = File.Exists(FullPath(
                root,
                "tools/Generated/scribe-emissions.v1.json"));
            Assert.True(retainedIsVisible);
            Assert.False(outsideProbeIsVisible);
            Assert.False(generatedEmissionIsVisible);
            var digest = Sha256(JsonSerializer.Serialize(new
            {
                Retained = retainedIsVisible,
                OutsideProbe = outsideProbeIsVisible,
                GeneratedEmission = generatedEmissionIsVisible,
            }));
            return VerifiedScribeEmissions.Create(
            [
                new ScribeEmissionRecord(
                    "D5/S0/Carrier/Probe",
                    "Blueprint/D5/S0/Carrier/Probe.scribe.cs",
                    digest,
                    "Blueprint/D5/S0/Carrier/Probe.md",
                    digest),
            ]);
        });
        return verifier.Verify(snapshot, EmptyReport(), RawChangeSet.Create([]));
    }

    private static void VerifyDirectoryState(RepositorySnapshot snapshot, bool expected)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.Equal(expected, Directory.Exists(FullPath(root, "Library")));
            Assert.Equal(expected, Directory.Exists(FullPath(root, "Problems")));
            Assert.Equal(expected, Directory.Exists(FullPath(
                root,
                "Meta/Digestion/backfill")));
            return VerifiedScribeEmissions.Empty;
        });
        verifier.Verify(snapshot, EmptyReport(), RawChangeSet.Create([]));
    }

    private static byte[] CapabilityBytes(VerifiedScribeEmissions capability)
    {
        Assert.True(capability.TryGet("D5/S0/Carrier/Probe", out var record));
        return JsonSerializer.SerializeToUtf8Bytes(record);
    }

    private static byte[] CapabilityBytes(
        VerifiedScribeEmissions capability,
        LeanAxiomReport report)
    {
        var records = DocumentDefinitions.All
            .Select(definition => capability.TryGet(
                definition.Document.Header.Gid.Value,
                out var record) ? record : null)
            .Where(static record => record is not null)
            .OrderBy(static record => record!.Gid, StringComparer.Ordinal)
            .ToArray();
        var references = report.Files
            .SelectMany(static file => file.Value.Declarations.Select(declaration =>
                file.Key.Value[..^".lean".Length]
                + "."
                + declaration.Name[(declaration.Name.LastIndexOf('.') + 1)..]))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .Select(reference => new
            {
                Reference = reference,
                Present = capability.ReferencesDeclaration(reference),
            })
            .ToArray();
        return JsonSerializer.SerializeToUtf8Bytes(new
        {
            Records = records,
            References = references,
            Latex = capability.DescribeLatexRecords,
        });
    }

    private static LeanAxiomReport ReportForDocuments(IEnumerable<ScribeDocument> documents)
    {
        var declarations = documents
            .SelectMany(static document => References(document.Content))
            .DistinctBy(static item => item.Reference.Value, StringComparer.Ordinal)
            .GroupBy(static item => item.Reference.Reference.Path.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => new LeanFileReport(
                    [],
                    group.Select(static item => new LeanDeclaration(
                            Selector(item.Reference),
                            item.ReportKind,
                            $"statement-v1(source={item.Reference.Value})",
                            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound")))
                        .ToImmutableArray()),
                StringComparer.Ordinal);
        return LeanAxiomReport.Create(declarations);
    }

    private static IEnumerable<ReferencedDeclaration> References(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var reference in References(section.Content)) yield return reference;
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.Statement is DescribeStatement.LeanDeclaration lean)
                    {
                        yield return new ReferencedDeclaration(lean.Value, ReportKindOf(describe));
                    }
                    foreach (var reference in References(describe.Content)) yield return reference;
                    break;
            }
        }
    }

    private static string Selector(LeanDeclarationRef reference) =>
        reference.Value.Replace('/', '.');

    private static string ReportKindOf(DocumentBlock.Describe describe) => describe.KindSource switch
    {
        DescribeKindSource.Authored authored => ReportKind(authored.Value),
        DescribeKindSource.ReportDerived derived => derived.Role switch
        {
            DescribeRole.Definition => "def",
            DescribeRole.Theorem => "theorem",
            DescribeRole.Proposition => "theorem",
            DescribeRole.Lemma => "theorem",
            DescribeRole.Remark => "theorem",
            _ => "theorem",
        },
        _ => "theorem",
    };

    private static string ReportKind(DescribeKind kind) => kind switch
    {
        DescribeKind.Definition => "def",
        DescribeKind.Theorem => "theorem",
        DescribeKind.Proposition => "theorem",
        DescribeKind.Lemma => "theorem",
        DescribeKind.Example => "theorem",
        DescribeKind.Remark => "theorem",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    private static LeanAxiomReport EmptyReport() => LeanAxiomReport.Create(
        new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

    private static RepositorySnapshot Snapshot(params RawRepositoryEntry[] entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;

    private static string FullPath(string root, string path) => Path.Combine(
        root,
        path.Replace('/', Path.DirectorySeparatorChar));

    private static string Sha256(string value) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));

    private static IReadOnlyList<(string RelativePath, string FullPath)> EnumerateDeclared(
        string repositoryRoot,
        string declaredPrefix) => StrataLint.Engine.GitIndexRepositoryFiles
        .Enumerate(repositoryRoot)
        .Where(file => file.RelativePath.StartsWith(
            declaredPrefix + "/",
            StringComparison.Ordinal))
        .ToArray();

    private readonly record struct ReferencedDeclaration(
        LeanDeclarationRef Reference,
        string ReportKind);
}
