using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenContentAddressTests
{
    [Fact]
    public void ProofOnlyRewritePreservesWitnessAndFrozenNodeIdentity()
    {
        const string firstSource = "theorem a : True := by trivial\n";
        var secondSource = firstSource;
        secondSource = "theorem a : True := by exact True.intro\n";
        var first = BuildCatalog(Module("A", source: firstSource));
        var second = BuildCatalog(Module("A", source: secondSource));

        var firstNode = Assert.Single(first.ClosedNodes);
        var secondNode = Assert.Single(second.ClosedNodes);
        Assert.NotEqual(firstNode.Attestation.SourceBlobOid, secondNode.Attestation.SourceBlobOid);
        Assert.Equal(firstNode.StatementId, secondNode.StatementId);
        Assert.Equal(firstNode.WitnessId, secondNode.WitnessId);
        Assert.Equal(firstNode.FrozenNodeId, secondNode.FrozenNodeId);

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
    public void WitnessV2PreimageContainsExactlyTheFiveIdentityFields()
    {
        var node = Assert.Single(BuildCatalog(Module(
            "A",
            axioms: new[] { "Classical.choice" })).ClosedNodes);
        var material = JsonSerializer.SerializeToElement(new
        {
            axiom_closure = node.AxiomClosure,
            imports = Array.Empty<string>(),
            module_path = node.RepoPath.Value,
            schema = "witness-v2",
            statement_id = node.StatementId.Value,
        });

        Assert.Equal(
            ["axiom_closure", "imports", "module_path", "schema", "statement_id"],
            material.EnumerateObject().Select(static property => property.Name));
        Assert.False(material.TryGetProperty("source_blob_oid", out _));
        Assert.False(material.TryGetProperty("source_sha256", out _));
        Assert.False(material.TryGetProperty("lean_toolchain_blob_oid", out _));
        Assert.False(material.TryGetProperty("lake_manifest_blob_oid", out _));
        Assert.Equal("witness-v2", material.GetProperty("schema").GetString());

        var expected = FrozenContentHash.Compute(
            FrozenHashDomains.Witness,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
        Assert.Equal(expected, node.WitnessId.Value);
    }

    [Fact]
    public void PinBlobOidChangesPreserveWitnessIdentity()
    {
        const string firstToolchain = "leanprover/lean4:v4.24.0\n";
        const string firstManifest = "{}\n";
        var secondToolchain = firstToolchain;
        var secondManifest = firstManifest;
        secondToolchain = "leanprover/lean4:v4.31.0\n";
        secondManifest = "{\"packages\":[]}\n";
        var first = BuildCatalogWithEnvironment(
            firstToolchain,
            "[package]\nname = \"fixture\"\n",
            firstManifest,
            GitOid('a'),
            GitOid('b'),
            Module("A"));
        var second = BuildCatalogWithEnvironment(
            secondToolchain,
            "[package]\nname = \"fixture\"\n",
            secondManifest,
            GitOid('a'),
            GitOid('b'),
            Module("A"));

        var firstNode = Assert.Single(first.ClosedNodes);
        var secondNode = Assert.Single(second.ClosedNodes);
        Assert.Equal(firstNode.StatementId, secondNode.StatementId);
        Assert.Equal(firstNode.Attestation.SourceBlobOid, secondNode.Attestation.SourceBlobOid);
        Assert.NotEqual(
            first.Environment.LeanToolchainBlobOid,
            second.Environment.LeanToolchainBlobOid);
        Assert.NotEqual(
            first.Environment.LakeManifestBlobOid,
            second.Environment.LakeManifestBlobOid);
        Assert.Equal(firstNode.WitnessId, secondNode.WitnessId);
    }

    [Fact]
    public void StatementIdChangeChangesWitnessIdentity()
    {
        const string source = "theorem a : True := by trivial\n";
        const string firstStatement = "True";
        var secondStatement = firstStatement;
        secondStatement = "False";
        var first = Assert.Single(BuildCatalog(
            ModuleWithReport("A", source, firstStatement)).ClosedNodes);
        var second = Assert.Single(BuildCatalog(
            ModuleWithReport("A", source, secondStatement)).ClosedNodes);

        Assert.Equal(first.Attestation.SourceBlobOid, second.Attestation.SourceBlobOid);
        Assert.NotEqual(first.StatementId, second.StatementId);
        Assert.NotEqual(first.WitnessId, second.WitnessId);
    }

    [Fact]
    public void AxiomClosureChangeChangesWitnessIdentity()
    {
        const string source = "theorem a : True := by trivial\n";
        var first = Assert.Single(BuildCatalog(Module("A", source)).ClosedNodes);
        var second = Assert.Single(BuildCatalog(Module(
            "A",
            source,
            axioms: new[] { "Classical.choice" })).ClosedNodes);

        Assert.Equal(first.Attestation.SourceBlobOid, second.Attestation.SourceBlobOid);
        Assert.Equal(first.StatementId, second.StatementId);
        Assert.NotEqual(first.AxiomClosure, second.AxiomClosure);
        Assert.NotEqual(first.WitnessId, second.WitnessId);
    }

    [Fact]
    public void ContentAddressBytesArePinnedOnAFixedFixture()
    {
        // Pin witness-v2 and derived frozen-node bytes for a representative dependency graph.
        var catalog = BuildCatalog(Module("A"), Module("B", imports: new[] { "A" }));

        var nodes = catalog.ClosedNodes
            .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(2, nodes.Length);
        var a = nodes[0];
        var b = nodes[1];
        Assert.Equal("sha256:2737dabb279d14181efe09f7531e5c4664421bdbc19bbcf8b588f8d71123954c", a.StatementId.Value);
        Assert.Equal("sha256:bced4890a6a5d0cfce247bb5608fbd2e1fd31a67f286ef45634b13e0bb09116b", a.WitnessId.Value);
        Assert.Equal("sha256:65ca68f9792e942e51248f5ba3853bf2aa68b2dee1339d705ecfeb72b9074424", a.FrozenNodeId.Value);
        Assert.Equal("sha256:211af3769c4571cac3b50ccaad89160fef4f94e790bc01fdc890d927c6b63112", b.StatementId.Value);
        Assert.Equal("sha256:d62be4f4f1020a5327aeee895906604afc45f47aafdf83a304365ddc807d9b0c", b.WitnessId.Value);
        Assert.Equal("sha256:a4c3e6cec8afccd31005f5e5647c768526ac07455028266264a4b6f16945107d", b.FrozenNodeId.Value);
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
        Assert.Equal("sha256:026d035ace228a479271d344acdf23b6f624a026456b1c135d8fc0243420b47f", c.WitnessId.Value);
        Assert.Equal("sha256:a921df0b56da97cda70c14f33eea1f5820368c1b8b0de02bbeb91dfa0d3a6ce6", c.FrozenNodeId.Value);
        Assert.Equal(
            new[]
            {
                "sha256:65ca68f9792e942e51248f5ba3853bf2aa68b2dee1339d705ecfeb72b9074424",
                "sha256:a4c3e6cec8afccd31005f5e5647c768526ac07455028266264a4b6f16945107d",
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
