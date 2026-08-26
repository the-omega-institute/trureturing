using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenContentAddressTests
{
    [Fact]
    public void ProofOnlyRewritePreservesStatementIdAndChangesWitnessAndFrozenNodeIds()
    {
        var first = BuildCatalog(Module("A", source: "theorem a : True := by trivial\n"));
        var second = BuildCatalog(Module("A", source: "theorem a : True := by exact True.intro\n"));

        var firstNode = Assert.Single(first.ClosedNodes);
        var secondNode = Assert.Single(second.ClosedNodes);
        Assert.Equal(firstNode.StatementId, secondNode.StatementId);
        Assert.NotEqual(firstNode.WitnessId, secondNode.WitnessId);
        Assert.NotEqual(firstNode.FrozenNodeId, secondNode.FrozenNodeId);

        const string source = "theorem a : True := by trivial\n";
        var raw = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.24.0\n"),
            RawRepositoryEntry.FromText("lake-manifest.json", "{}\n"),
            RawRepositoryEntry.FromText(PathFor("A"), source),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [PathFor("A")] = new(
                ["D5.S0.Carrier.Missing"],
                [new LeanDeclaration("a", "theorem", "True", []) { NameKey = "ns(n0,1:a)" }]),
            [PathFor("Missing")] = new([], []),
        });
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, report)).Capability;
        var environment = new FrozenEnvironmentAttestation(
            GitOid('a'),
            GitOid('b'),
            GitBlobOid("leanprover/lean4:v4.24.0\n"),
            GitBlobOid("{}\n"));
        var states = LeanTruthStates.Resolve(snapshot, closure);
        var adjacency = LeanImportAdjacency.Build(snapshot, closure);

        Assert.False(snapshot.Files.ContainsKey(RepoPathFor("Missing")));
        var danglingImportCatalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(
                snapshot,
                closure,
                states,
                adjacency,
                environment,
                [new FrozenModuleAttestation(RepoPathFor("A"), GitBlobOid(source))])).Capability;
        Assert.Empty(Assert.Single(danglingImportCatalog.ClosedNodes).PrerequisiteFrozenNodeIds);
    }

    [Fact]
    public void ContentAddressBytesArePinnedOnAFixedFixture()
    {
        // #3030 phase 1 invariant: shrinking the truth-DAG node domain to managed Lean modules
        // must not move a single frozen address byte. The fixture snapshot deliberately carries
        // non-Lean files (lean-toolchain, lakefile.toml, lake-manifest.json), so these literals
        // span the domain change: they were captured before the shrink and must hold after it.
        var catalog = BuildCatalog(Module("A"), Module("B", imports: new[] { "A" }));

        var nodes = catalog.ClosedNodes
            .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(2, nodes.Length);
        var a = nodes[0];
        var b = nodes[1];
        Assert.Equal("sha256:2737dabb279d14181efe09f7531e5c4664421bdbc19bbcf8b588f8d71123954c", a.StatementId.Value);
        Assert.Equal("sha256:0d37e262a8c68df2ebd0e192b50b7167e5b697bb36d6f0c02649ede0e9844d9e", a.WitnessId.Value);
        Assert.Equal("sha256:e6a10a73d813973ee49f0fa6bbb0ae9d2c3b2c7931a283509c1e3e97df05acde", a.FrozenNodeId.Value);
        Assert.Equal("sha256:211af3769c4571cac3b50ccaad89160fef4f94e790bc01fdc890d927c6b63112", b.StatementId.Value);
        Assert.Equal("sha256:6fbd91738bbd18aeb82433e85e57a82611c1bdf456463a51dbcaedfc483a838f", b.WitnessId.Value);
        Assert.Equal("sha256:7c7584c4367278ce869226f688f6b67bfc072742811497c19f2d7fb197a8c15e", b.FrozenNodeId.Value);
        var prerequisite = Assert.Single(b.PrerequisiteFrozenNodeIds);
        Assert.Equal(a.FrozenNodeId.Value, prerequisite.Value);

        var multiPrerequisiteCatalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }),
            Module("C", imports: new[] { "A", "B" }));
        var c = multiPrerequisiteCatalog.ClosedNodes
            .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
            .ToArray()[2];
        Assert.Equal("sha256:7fe10a833c778c19c4bf29a36f7a07486253042f63965d955ead898161fe7094", c.StatementId.Value);
        Assert.Equal("sha256:bc2cc19c308ddbe355363aafa34dff87472b0f5cd4d35b5fb89f771b3d9c6a4b", c.WitnessId.Value);
        Assert.Equal("sha256:65df0e281883e52131685be2fe5187a763c89314b8bc3f414e4f29c47cb57585", c.FrozenNodeId.Value);
        Assert.Equal(
            new[]
            {
                "sha256:7c7584c4367278ce869226f688f6b67bfc072742811497c19f2d7fb197a8c15e",
                "sha256:e6a10a73d813973ee49f0fa6bbb0ae9d2c3b2c7931a283509c1e3e97df05acde",
            },
            c.PrerequisiteFrozenNodeIds.Select(static id => id.Value));
    }

    [Fact]
    public void FreezeCarriesDeclarationStatementIdsWithoutCopyingStatementMaterial()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var line = Lines(bytes)[1];
        using var document = JsonDocument.Parse(line.AsMemory(0, line.Length - 1));

        var payload = document.RootElement.GetProperty("payload");
        Assert.True(payload.TryGetProperty("declaration_statement_ids", out var declarationStatementIds));
        var reference = Assert.Single(declarationStatementIds.EnumerateArray());
        Assert.False(reference.TryGetProperty("declaration_name", out _));
        Assert.Equal("ns(n0,1:a)", reference.GetProperty("declaration_name_key").GetString());
        Assert.Equal("theorem", reference.GetProperty("kind").GetString());
        Assert.Matches(
            "^sha256:[0-9a-f]{64}$",
            reference.GetProperty("statement_id").GetString());
        Assert.DoesNotContain("statement_material", payload.GetRawText(), StringComparison.Ordinal);
    }

    [Fact]
    public void ForgedDeclarationStatementIdFailsAfterCanonicalEventRehash()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var lines = Lines(bytes);
        using var genesisDocument = JsonDocument.Parse(
            lines[0].AsMemory(0, lines[0].Length - 1));
        using var freezeDocument = JsonDocument.Parse(
            lines[1].AsMemory(0, lines[1].Length - 1));
        var payload = JsonNode.Parse(
            freezeDocument.RootElement.GetProperty("payload").GetRawText())!.AsObject();
        payload["declaration_statement_ids"]!.AsArray()[0]!["statement_id"] =
            Sha256("forged-declaration");
        var forgedLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(payload),
            genesisDocument.RootElement.GetProperty("event_hash").GetString()!,
            1).Bytes;
        var forged = lines[0].Concat(forgedLine).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(forged)).Syntax,
                catalog));

        Assert.Contains("recomputed material", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void RehashedGenesisFreezeReorderingFailsCanonicalEventOrder()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var lines = Lines(bytes);
        using var genesisDocument = JsonDocument.Parse(
            lines[0].AsMemory(0, lines[0].Length - 1));
        using var firstFreezeDocument = JsonDocument.Parse(
            lines[1].AsMemory(0, lines[1].Length - 1));
        using var secondFreezeDocument = JsonDocument.Parse(
            lines[2].AsMemory(0, lines[2].Length - 1));
        var first = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            secondFreezeDocument.RootElement.GetProperty("payload"),
            genesisDocument.RootElement.GetProperty("event_hash").GetString()!,
            1);
        var second = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            firstFreezeDocument.RootElement.GetProperty("payload"),
            first.Hash,
            2);
        var reordered = lines[0].Concat(first.Bytes).Concat(second.Bytes).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(reordered)).Syntax,
                catalog));

        Assert.Contains("order", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }
}
