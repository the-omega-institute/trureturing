using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// ProductionEnvironmentCoverTests 的后半:cover 拒绝路径一族。
// 分出来的直接理由是余量:宿主原 795 行,离 SL-003 的 800 行硬线只剩 5 行。
// 该类本就是 partial,故切分不动类声明。
// 切点用「缩进 4 的真方法收尾 ∧ 后接空行 ∧ 再后是缩进 4 的特性行」判定,
// 全文件 16 处候选取最接近中点者(第 416 行)。

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomLeavesLedgerBytesUnchangedWhenAGateRejects()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { VerifyScribe = false });
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("COVER_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverAtomAlwaysValidatesCurrentCoverageButScopesScribeBacklog(string mismatchCode)
    {
        const string siblingModuleGid = "D5/S0/Carrier/CoverSibling";
        const string siblingGid = siblingModuleGid + ".sibling";
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            SecondaryTarget = (siblingModuleGid, "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                [siblingGid],
                [siblingGid],
                ["historical-uncovered-clause"]),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create(["D5/S0/Carrier/Probe.lean"]));

        var result = environment.CoverAtom(CoverArgs(inputs));

        if (mismatchCode == "coverage-target-mismatch")
        {
            Assert.False(result.Success);
            Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
        else
        {
            Assert.True(
                result.Success,
                $"unrelated-scribe-drift-must-not-block-cover ({mismatchCode}): {result.Error}");
            Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
            Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
    }

    private static CoverInputs DirectoryInputs(CoverInputs inputs) => inputs with
    {
        Files = DirectoryLedgerTestSupport.Project(inputs.Files),
        Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
    };

    private static Dictionary<string, string> FilesWithLedgerFromRoot(
        IReadOnlyDictionary<string, string> files,
        string repositoryRoot)
    {
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            result,
            BackfillInventoryLoader.LoadRoot(repositoryRoot));
        return result;
    }

    private static CoverInputs WithSiblingReceiptMismatch(CoverInputs inputs, string mismatchCode)
    {
        var entries = inputs.Document.RequireDigestionEntries();
        var siblingAtomId = entries.Any(entry => entry.AtomId == CoverWorld.OtherAtomId)
            ? CoverWorld.OtherAtomId
            : CoverWorld.UnrelatedAtomId;
        var siblingEntry = Assert.Single(
            entries,
            entry => entry.AtomId == siblingAtomId);
        var siblingGid = Assert.Single(siblingEntry.CoverageGids);
        var documentGid = ScribeEmissionAttestation.DocumentGid(siblingGid);
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verified));
        var targetStatementId = FrozenStatementReceiptTestData.Resolve(inputs.Files, siblingGid);
        var mismatchStatementId = FrozenStatementReceiptTestData.Id('0');
        BackfillInventoryDocument WithMismatch(BackfillInventoryDocument document) =>
            document.WithDigestionSources(document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Coverage =
                            [
                                new DigestionCoverageEdge(
                                    siblingGid,
                                    mismatchCode == "coverage-target-mismatch"
                                        ? mismatchStatementId
                                        : targetStatementId),
                            ],
                            Receipts = entry.Receipts with
                            {
                                Scribe =
                                [
                                    new DigestionScribeReceipt(
                                        siblingGid,
                                        mismatchCode == "scribe-definition-mismatch"
                                            ? mismatchStatementId
                                            : verified.DefinitionSha256,
                                        mismatchCode == "scribe-emission-mismatch"
                                            ? mismatchStatementId
                                            : verified.EmissionSha256),
                                ],
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());

        var document = WithMismatch(inputs.Document);
        var baselineSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Baseline))).Snapshot;
        var baselineDocument = WithMismatch(BackfillInventoryLoader.Load(baselineSnapshot));
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baseline, baselineDocument);
        return inputs with
        {
            Files = files,
            Baseline = baseline,
            Document = document,
        };
    }

    private static CoverInputs WithReceiptMismatchAtForkPoint(
        CoverInputs inputs,
        string mismatchCode,
        bool byteIdenticalBaseline = false)
    {
        var current = WithSiblingReceiptMismatch(inputs, mismatchCode);
        var baseline = byteIdenticalBaseline
            ? new Dictionary<string, string>(current.Files, StringComparer.Ordinal)
            : new Dictionary<string, string>(current.Baseline, StringComparer.Ordinal);
        if (!byteIdenticalBaseline)
        {
            DirectoryLedgerTestSupport.ReplaceWithProjection(baseline, current.Document);
        }

        return current with { Baseline = baseline };
    }

    private static CoverInputs WithSiblingDuplicateCoverageReceipt(CoverInputs inputs)
    {
        var siblingAtomId = CoverWorld.OtherAtomId;
        var documentGid = inputs.Gid[..inputs.Gid.LastIndexOf('.')];
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verified));
        var targetStatementId = FrozenStatementReceiptTestData.Resolve(inputs.Files, inputs.Gid);
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Coverage =
                            [
                                new DigestionCoverageEdge(inputs.Gid, targetStatementId),
                                new DigestionCoverageEdge(inputs.Gid, targetStatementId),
                            ],
                            Receipts = entry.Receipts with
                            {
                                Scribe =
                                [
                                    new DigestionScribeReceipt(
                                        inputs.Gid,
                                        verified.DefinitionSha256,
                                        verified.EmissionSha256),
                                ],
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return inputs with { Files = files, Document = document };
    }

    private static ProductionCliEnvironment BuildCoverEnvironment(
        string repositoryRoot,
        CoverInputs inputs,
        IReadOnlyDictionary<string, string> currentFiles,
        RawChangeSet? changes = null)
    {
        return new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(
                changes ?? RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));
    }

    private static void AssertProductionScribeVerifierMaterializesOnlyTheCapturedSnapshot()
    {
        string? materializedRoot = null;
        string? observed = null;
        string? observedProjectionFixture = null;
        var verification = VerifiedScribeEmissions.Empty;
        var callback = new Func<string, LeanAxiomReport, VerifiedScribeEmissions>((root, _) =>
        {
            materializedRoot = root;
            observed = File.ReadAllText(Path.Combine(root, "captured", "probe.txt"), Encoding.UTF8);
            observedProjectionFixture = File.ReadAllText(
                Path.Combine(root, "Golden", "Projection", "statement-projection-pilot-v1.json"),
                Encoding.UTF8);
            return verification;
        });
        var verifier = new ProductionScribeEmissionVerifier(callback);
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var fixtureFiles = new[]
        {
            "statement-projection-pilot-v1.json",
            "statement-projection-expansion-v1.json",
        }.Select(name =>
        {
            var path = $"Golden/Projection/{name}";
            return (Path: path, Content: File.ReadAllText(
                Path.Combine(repositoryRoot, path.Replace('/', Path.DirectorySeparatorChar)),
                Encoding.UTF8));
        }).ToArray();
        var declarations = ImmutableArray.CreateBuilder<LeanDeclaration>();
        foreach (var fixture in fixtureFiles)
        {
            using var document = JsonDocument.Parse(fixture.Content);
            foreach (var declaration in document.RootElement
                         .GetProperty("declarations")
                         .EnumerateArray())
            {
                declarations.Add(new LeanDeclaration(
                    declaration.GetProperty("name").GetString()!,
                    declaration.GetProperty("kind").GetString()!,
                    declaration.GetProperty("type").GetString()!,
                    []));
            }
        }
        var snapshotEntries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText("captured/probe.txt", "captured bytes\n"),
        };
        snapshotEntries.AddRange(fixtureFiles.Select(static fixture =>
            RawRepositoryEntry.FromText(fixture.Path, fixture.Content)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(snapshotEntries))).Snapshot;

        var actual = verifier.Verify(snapshot, LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>
            {
                ["D5/ProjectionFixture.lean"] = new([], declarations.ToImmutable()),
            }));

        Assert.Same(verification, actual);
        Assert.Equal("captured bytes\n", observed);
        Assert.Equal(fixtureFiles[0].Content, observedProjectionFixture);
        Assert.NotNull(materializedRoot);
        Assert.False(Directory.Exists(materializedRoot));
    }

    private static string[] CoverArgs(CoverInputs inputs) =>
        ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"];
}
