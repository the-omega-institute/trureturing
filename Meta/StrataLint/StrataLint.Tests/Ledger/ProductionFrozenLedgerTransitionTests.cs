using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string AcceptedPrefix = FrozenLedgerChangeClassifier.AcceptedRoot + "/";

    // 文件名约定:裸摘要,不含 "sha256:" 前缀。冒号在 Windows 上是保留字符,
    // 且仓内 CAS 先例 Meta/Digestion/atoms/sha256/<64hex> 同样是裸摘要。
    [Fact]
    public void AcceptedFileNameCarriesTheBareDigestWithoutTheAlgorithmPrefix()
    {
        var digest = new string('a', 64);
        var identity = "sha256:" + digest;
        Assert.Equal(digest + ".json", FrozenLedgerChangeClassifier.AcceptedFileName(identity));
        Assert.DoesNotContain(':', FrozenLedgerChangeClassifier.AcceptedPath(identity));
    }

    [Fact]
    public void ProductionValidatorAcceptsContentAddressedLedgerMigration()
    {
        var fixture = MigratedFixture();

        var outcome = Validate(fixture, CreateGateway(fixture));
        Assert.True(outcome is null, PositiveFailureMessage(outcome));
        Assert.Null(outcome);
    }

    [Fact]
    public void ProductionValidatorRecomputesEveryContentAddressedEventHash()
    {
        var fixture = MigratedFixture();
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Freeze");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        node["event_hash"] = FrozenLedgerTestData.Sha256("forged-unique-hash");
        fixture.CurrentFiles[path] = node.ToJsonString() + "\n";

        AssertTransitionRejected(fixture, "event_hash does not match canonical content");
    }

    [Fact]
    public void ProductionValidatorRequiresContentAddressedSchemaV2()
    {
        var fixture = MigratedFixture();
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Freeze");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        node["schema_version"] = 1;
        fixture.CurrentFiles[path] = node.ToJsonString() + "\n";

        AssertTransitionRejected(fixture, "schema_version must be 2");
    }

    [Fact]
    public void ProductionValidatorRejectsChangedMigrationPayload()
    {
        var fixture = MigratedFixture();
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) != "Genesis");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        node["payload"]!["evaluation"] = "epsilon";
        RewriteV2(fixture, path, node);

        AssertTransitionRejected(fixture, "payload differs from protected baseline");
    }

    [Fact]
    public void ProductionValidatorRejectsMissingMigrationFile()
    {
        var fixture = MigratedFixture();
        fixture.CurrentFiles.Remove(fixture.CurrentFiles.Keys.Last(static path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)));

        AssertTransitionRejected(fixture, "not a bijection");
    }

    [Fact]
    public void ProductionValidatorRejectsExtraMigrationFile()
    {
        var fixture = MigratedFixture();
        var source = fixture.CurrentFiles.Single(static item =>
            item.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(item.Value) == "Freeze").Value;
        var node = JsonNode.Parse(source)!.AsObject();
        node["payload"]!["frozen_node_id"] = "zeta";
        AddV2(fixture, "zeta", node);

        AssertTransitionRejected(fixture, "not a bijection");
    }

    [Fact]
    public void ContentAddressedLoaderRejectsFileNameThatDoesNotMatchIdentity()
    {
        var fixture = MigratedFixture();
        var item = fixture.CurrentFiles.Single(static pair =>
            pair.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(pair.Value) != "Genesis");
        fixture.CurrentFiles.Remove(item.Key);
        fixture.CurrentFiles[AcceptedPrefix + "epsilon.json"] = item.Value;

        AssertTransitionRejected(fixture, "file name does not match event identity");
    }

    [Fact]
    public void ContentAddressedLoaderRejectsDuplicateIdentity()
    {
        var fixture = MigratedFixture();
        var item = fixture.CurrentFiles.Single(static pair =>
            pair.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(pair.Value) != "Genesis");
        var node = JsonNode.Parse(item.Value)!.AsObject();
        node["payload"]!["evaluation"] = "epsilon";
        AddV2(fixture, "zeta", node);

        AssertTransitionRejected(fixture, "identity is duplicated");
    }

    [Fact]
    public void ContentAddressedLoaderRejectsDuplicateEventHash()
    {
        var fixture = MigratedFixture();
        var source = fixture.CurrentFiles.Single(static pair =>
            pair.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(pair.Value) != "Genesis").Value;
        fixture.CurrentFiles[AcceptedPrefix + "zeta.json"] = source;

        AssertTransitionRejected(fixture, "event_hash is duplicated");
    }

    [Fact]
    public void ContentAddressedLoaderRejectsOldAttestationHashReference()
    {
        var fixture = MigratedFixture(withLegacyReattest: true);
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Reattest");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        var oldFreeze = LegacyLines(fixture).Single(static item => item["event_type"]!.GetValue<string>() == "Freeze");
        node["payload"]!["previous_attestation_event_hash"] = oldFreeze["event_hash"]!.GetValue<string>();
        RewriteV2(fixture, path, node);

        AssertTransitionRejected(fixture, "old attestation hash mapping");
    }

    [Fact]
    public void ContentAddressedLoaderRejectsUnclosedPrerequisiteDag()
    {
        var fixture = MigratedFixture();
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) != "Genesis");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        node["payload"]!["prerequisite_frozen_node_ids"] = new JsonArray("delta");
        RewriteV2(fixture, path, node);

        AssertTransitionRejected(fixture, "closed dependency DAG");
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ProductionValidatorRejectsDualOrAbsentLedgerShapes(bool dualShape)
    {
        var fixture = MigratedFixture();
        if (dualShape)
        {
            fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath] =
                fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath];
        }
        else
        {
            foreach (var path in fixture.CurrentFiles.Keys
                .Where(static path => path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)).ToArray())
            {
                fixture.CurrentFiles.Remove(path);
            }
        }

        if (dualShape)
        {
            AssertTransitionRejected(fixture, "frozen ledger shape is invalid");
        }
        else
        {
            AssertSl008Rejection(
                Validate(fixture, CreateGateway(fixture)),
                "frozen ledger is missing from current or protected baseline");
        }
    }

    [Fact]
    public void ProductionValidatorPreservesMissingDiagnosticWhenBothShapesAreAbsent()
    {
        var fixture = MigratedFixture();
        fixture.BaselineFiles.Remove(FrozenLedgerChangeClassifier.LedgerPath);
        foreach (var path in fixture.CurrentFiles.Keys
            .Where(static path => path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)).ToArray())
        {
            fixture.CurrentFiles.Remove(path);
        }

        AssertSl008Rejection(
            Validate(fixture, CreateGateway(fixture)),
            "frozen ledger is missing from current or protected baseline");
    }

    [Fact]
    public void ProductionValidatorRejectsMixedAcceptedDirectoryContents()
    {
        var fixture = MigratedFixture();
        fixture.CurrentFiles[AcceptedPrefix + "epsilon.txt"] = "{}\n";

        AssertTransitionRejected(fixture, "frozen ledger shape is invalid");
    }

    [Fact]
    public void ProductionValidatorAcceptsMigrationContainingLegacyReattestPayload()
    {
        var fixture = MigratedFixture(withLegacyReattest: true);

        var outcome = Validate(fixture, CreateGateway(fixture));
        Assert.True(outcome is null, PositiveFailureMessage(outcome));
        Assert.Null(outcome);
    }

    [Fact]
    public void ProductionValidatorAcceptsAcceptedOnlyLedgerOnTheDayAfterMigration()
    {
        var fixture = SteadyStateFixture();

        var outcome = Validate(fixture, CreateGateway(fixture));

        Assert.True(outcome is null, PositiveFailureMessage(outcome));
        Assert.Null(outcome);
    }

    [Fact]
    public void ProductionValidatorAcceptsAppendOnlyAcceptedEventAfterMigration()
    {
        var fixture = SteadyStateFixture(withAppendedReattest: true);

        var outcome = Validate(fixture, CreateGateway(fixture));

        Assert.True(outcome is null, PositiveFailureMessage(outcome));
        Assert.Null(outcome);
    }

    [Fact]
    public void ProductionValidatorRejectsDeletedAcceptedBaselineEvent()
    {
        var fixture = SteadyStateFixture(withAppendedReattest: true);
        fixture.CurrentFiles.Remove(fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Genesis"));

        AssertTransitionRejected(fixture, "does not retain protected baseline file byte-for-byte");
    }

    [Fact]
    public void ProductionValidatorRejectsModifiedAcceptedBaselineEventBytes()
    {
        var fixture = SteadyStateFixture();
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Genesis");
        fixture.CurrentFiles[path] = fixture.CurrentFiles[path][..^1] + " \n";

        AssertTransitionRejected(fixture, "does not retain protected baseline file byte-for-byte");
    }

    [Fact]
    public void ProductionValidatorRejectsForgedAppendedAcceptedEventHash()
    {
        var fixture = SteadyStateFixture(withAppendedReattest: true);
        var path = fixture.CurrentFiles.Keys.Single(path =>
            path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(fixture.CurrentFiles[path]) == "Reattest");
        var node = JsonNode.Parse(fixture.CurrentFiles[path])!.AsObject();
        node["event_hash"] = FrozenLedgerTestData.Sha256("forged-unique-hash");
        fixture.CurrentFiles[path] = node.ToJsonString() + "\n";

        AssertTransitionRejected(fixture, "event_hash does not match canonical content");
    }

    [Fact]
    public void ProductionValidatorRejectsAppendedAcceptedEventWithMissingPrerequisite()
    {
        var fixture = SteadyStateFixture();
        var source = fixture.CurrentFiles.Single(static item =>
            item.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)
            && EventType(item.Value) == "Genesis").Value;
        var node = JsonNode.Parse(source)!.AsObject();
        node["event_type"] = "Freeze";
        node["payload"] = new JsonObject
        {
            ["frozen_node_id"] = "zeta",
            ["prerequisite_frozen_node_ids"] = new JsonArray("epsilon"),
        };
        AddV2(fixture, "zeta", node);

        AssertTransitionRejected(fixture, "closed dependency DAG");
    }

    [Fact]
    public void ProductionValidatorRejectsAcceptedOnlyBaselineReturningToLegacy()
    {
        var fixture = MigratedFixture();
        var legacy = fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath];
        ReplaceBaselineWithCurrentAcceptedFiles(fixture);
        fixture.CurrentFiles.Clear();
        foreach (var item in fixture.BaselineFiles.Where(static item =>
            !item.Key.StartsWith(AcceptedPrefix, StringComparison.Ordinal)))
        {
            fixture.CurrentFiles[item.Key] = item.Value;
        }

        fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath] = legacy;

        AssertTransitionRejected(fixture, "frozen ledger shape is invalid");
    }

    [Theory]
    [InlineData("dual")]
    [InlineData("absent")]
    [InlineData("invalid")]
    public void ProductionValidatorRejectsInvalidAcceptedOnlySteadyStateShape(string shape)
    {
        var fixture = SteadyStateFixture();
        if (shape == "dual")
        {
            fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath] = "{}\n";
        }
        else if (shape == "absent")
        {
            foreach (var path in fixture.CurrentFiles.Keys
                .Where(static path => path.StartsWith(AcceptedPrefix, StringComparison.Ordinal)).ToArray())
            {
                fixture.CurrentFiles.Remove(path);
            }
        }
        else
        {
            fixture.CurrentFiles[AcceptedPrefix + "epsilon.txt"] = "{}\n";
        }

        AssertTransitionRejected(fixture, "frozen ledger shape is invalid");
    }

    private static FrozenValidatorFixture MigratedFixture(bool withLegacyReattest = false)
    {
        var fixture = CreateFrozenValidatorFixture();
        if (withLegacyReattest)
        {
            AppendCurrentReattestation(fixture);
            fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath] =
                fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath];
        }

        var legacy = LegacyLines(fixture);
        fixture.CurrentFiles.Remove(FrozenLedgerChangeClassifier.LedgerPath);
        var oldToNew = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var item in legacy)
        {
            var payload = item["payload"]!.AsObject();
            if (payload["previous_attestation_event_hash"] is JsonValue previous)
            {
                payload["previous_attestation_event_hash"] = oldToNew[previous.GetValue<string>()];
            }

            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                item["event_type"]!.GetValue<string>(),
                JsonSerializer.SerializeToElement(payload));
            oldToNew.Add(item["event_hash"]!.GetValue<string>(), encoded.Hash);
            var identity = payload["frozen_node_id"]?.GetValue<string>() ?? encoded.Hash;
            fixture.CurrentFiles[FrozenLedgerChangeClassifier.AcceptedPath(identity)] =
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        }

        return fixture;
    }

    private static FrozenValidatorFixture SteadyStateFixture(bool withAppendedReattest = false)
    {
        var fixture = MigratedFixture(withAppendedReattest);
        var baseline = MigratedFixture();
        fixture.BaselineFiles.Clear();
        foreach (var item in baseline.CurrentFiles)
        {
            fixture.BaselineFiles[item.Key] = item.Value;
        }

        return fixture;
    }

    private static void ReplaceBaselineWithCurrentAcceptedFiles(FrozenValidatorFixture fixture)
    {
        fixture.BaselineFiles.Clear();
        foreach (var item in fixture.CurrentFiles)
        {
            fixture.BaselineFiles[item.Key] = item.Value;
        }
    }

    private static JsonObject[] LegacyLines(FrozenValidatorFixture fixture) =>
        fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath]
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => JsonNode.Parse(line)!.AsObject())
            .ToArray();

    private static void RewriteV2(FrozenValidatorFixture fixture, string path, JsonObject node)
    {
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            node["event_type"]!.GetValue<string>(),
            JsonSerializer.SerializeToElement(node["payload"]));
        var text = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        if (node["payload"]!["frozen_node_id"] is null)
        {
            fixture.CurrentFiles.Remove(path);
            fixture.CurrentFiles[FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash)] = text;
        }
        else
        {
            fixture.CurrentFiles[path] = text;
        }
    }

    private static void AddV2(FrozenValidatorFixture fixture, string identity, JsonObject node)
    {
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            node["event_type"]!.GetValue<string>(),
            JsonSerializer.SerializeToElement(node["payload"]));
        fixture.CurrentFiles[FrozenLedgerChangeClassifier.AcceptedPath(identity)] =
            Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
    }

    private static void AssertTransitionRejected(FrozenValidatorFixture fixture, string messageFragment)
    {
        var outcome = Validate(fixture, CreateGateway(fixture));
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(messageFragment, Assert.Single(rejected.Diagnostics).Message, StringComparison.Ordinal);
    }

    private static string? PositiveFailureMessage(AdmissionOutcome? outcome) =>
        outcome is AdmissionOutcome.RuleRejected rejected
            ? Assert.Single(rejected.Diagnostics).Message
            : null;

    private static string EventType(string json) =>
        JsonNode.Parse(json)!["event_type"]!.GetValue<string>();
}
