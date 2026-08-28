using System.Collections.Immutable;
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
    public void ProofOnlyRewritePreservesStatementIdAndChangesWitnessAndFrozenNodeIds()
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
    public void WitnessV1PreimageContainsSourceAndPinnedEnvironmentIdentity()
    {
        const string source = "theorem a : True := by trivial\n";
        var catalog = BuildCatalog(Module(
            "A",
            source,
            axioms: new[] { "Classical.choice" }));
        var node = Assert.Single(catalog.ClosedNodes);
        var material = JsonSerializer.SerializeToElement(new
        {
            axiom_closure = node.AxiomClosure,
            imports = Array.Empty<string>(),
            lake_manifest_blob_oid = catalog.Environment.LakeManifestBlobOid,
            lean_toolchain_blob_oid = catalog.Environment.LeanToolchainBlobOid,
            module_path = node.RepoPath.Value,
            schema = "witness-v1",
            source_blob_oid = node.Attestation.SourceBlobOid,
            source_sha256 = Sha256(source),
            statement_id = node.StatementId.Value,
        });

        Assert.Equal(
            [
                "axiom_closure", "imports", "lake_manifest_blob_oid",
                "lean_toolchain_blob_oid", "module_path", "schema", "source_blob_oid",
                "source_sha256", "statement_id",
            ],
            material.EnumerateObject().Select(static property => property.Name));
        Assert.Equal("witness-v1", material.GetProperty("schema").GetString());

        var expected = FrozenContentHash.Compute(
            FrozenHashDomains.Witness,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
        Assert.Equal(expected, node.WitnessId.Value);
    }

    [Fact]
    public void PinBlobOidChangesChangeWitnessIdentity()
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
        Assert.NotEqual(firstNode.WitnessId, secondNode.WitnessId);
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
        // Pin witness-v1 and derived frozen-node bytes for a representative dependency graph.
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
        var files = EventFiles(catalog);
        var freeze = Assert.Single(LoadEvents(files), static item => item.EventType == "Freeze");
        var file = files.Single(item => item.Path == freeze.SourcePath);
        using var document = JsonDocument.Parse(file.RawBytes.AsSpan()[..^1].ToArray());

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
        var emptyCatalog = BuildCatalog();
        var catalog = BuildCatalog(Module("A"));
        var baselineFiles = EventFiles(emptyCatalog);
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            baselineFiles.ToImmutableDictionary(static file => file.Path)));
        var baseline = baseView.ToWriterBaseline();
        var draft = Assert.Single(FrozenLedgerGenerator.MissingFreezes(baseline, catalog));
        var payload = JsonNode.Parse(
            draft.Payload.GetRawText())!.AsObject();
        payload["declaration_statement_ids"]!.AsArray()[0]!["statement_id"] =
            Sha256("forged-declaration");
        var forgedFile = EventFile("Freeze", JsonSerializer.SerializeToElement(payload));
        var forged = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
            baseView,
            [forgedFile],
            "forged test event");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(forged, baseline, catalog));

        Assert.Contains("recomputed material", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }
}
