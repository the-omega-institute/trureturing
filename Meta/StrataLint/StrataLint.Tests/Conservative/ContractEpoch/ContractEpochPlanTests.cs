using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ContractEpochPlanTests
{
    private const string Path = "Meta/StrataLint/Golden/values-kernels.toml";
    private static readonly string Receipt = "sha256:" + new string('a', 64);
    private static readonly string Proof = "sha256:" + new string('b', 64);
    private static readonly string PrePolicy = "sha256:" + new string('c', 64);
    private static readonly string PostPolicy = "sha256:" + new string('d', 64);
    private static readonly string BaselineTree = "git-sha1:" + new string('e', 40);

    [Fact]
    public void TransitionPlanIsSealedToTheTwoVersionedCases()
    {
        var cases = typeof(TransitionPlan).GetNestedTypes(
                BindingFlags.Public | BindingFlags.NonPublic)
            .Where(static item => item.BaseType == typeof(TransitionPlan))
            .Select(static item => item.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(["AuthorityDischargeV1", "CustodyTransferV1"], cases);
    }

    [Fact]
    public void CustodyTransferRoundTripsCanonicalBytes()
    {
        TransitionPlan plan = new TransitionPlan.CustodyTransferV1(
            [Path],
            new MachineCustodian(MachineCustodianKind.Loader, "Meta/Loader.cs"),
            Receipt);

        var first = TransitionPlanCodec.Write(plan);
        var decoded = TransitionPlanCodec.Read(first.AsSpan());
        var second = TransitionPlanCodec.Write(decoded);

        Assert.IsType<TransitionPlan.CustodyTransferV1>(decoded);
        Assert.Equal(first.ToArray(), second.ToArray());
    }

    [Fact]
    public void AuthorityDischargeSupportsAnExactRuleObligation()
    {
        TransitionPlan plan = new TransitionPlan.AuthorityDischargeV1(
            [],
            "SL-016",
            Proof);

        var decoded = Assert.IsType<TransitionPlan.AuthorityDischargeV1>(
            TransitionPlanCodec.Read(TransitionPlanCodec.Write(plan).AsSpan()));

        Assert.Empty(decoded.ExactPaths);
        Assert.Equal("SL-016", decoded.RuleObligation);
    }

    [Theory]
    [InlineData("Meta/StrataLint/Golden/*.toml")]
    [InlineData("Meta/StrataLint/Golden/")]
    [InlineData("meta/stratalint/golden/values-kernels.toml")]
    public void NonExactOrCaseCollidingPathsFailClosed(string invalidPath)
    {
        var json = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            exact_paths = new[] { Path, invalidPath },
            kind = "CustodyTransferV1",
            new_custodian = new
            {
                kind = "loader",
                reference = "Meta/Loader.cs",
            },
            receipt = Receipt,
        }));

        var exception = Assert.Throws<FormatException>(() =>
            TransitionPlanCodec.Read(json.AsSpan()));

        Assert.Contains("exact path", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void DischargeScopeMustChoosePathsOrRuleButNotBoth()
    {
        var exception = Assert.Throws<ArgumentException>(() =>
            new TransitionPlan.AuthorityDischargeV1([Path], "SL-016", Proof));

        Assert.Contains("exactly one", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("Meta/NotAC0Anchor.txt")]
    [InlineData("c0/")]
    [InlineData("c0/controller\nforged")]
    public void C0CustodianRequiresAnExactTowerAnchorRecord(string invalidReference)
    {
        var exception = Assert.Throws<ArgumentException>(() =>
            new MachineCustodian(MachineCustodianKind.C0Anchor, invalidReference));

        Assert.Contains("C0 anchor", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SemanticallyUnsortedExactPathsAreNotCanonicalPlanBytes()
    {
        const string earlierPath = "Blueprint/D5/S0/Carrier/Ring.md";
        var bytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            exact_paths = new[] { Path, earlierPath },
            kind = "AuthorityDischargeV1",
            unreachability_proof_ref = Proof,
        }));

        var exception = Assert.Throws<FormatException>(() =>
            TransitionPlanCodec.Read(bytes.AsSpan()));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void LedgerAllowsOneBaseRegisteredConsumption()
    {
        var registration = Registration("CONTRACT-001");
        var baseline = ContractEpochLedgerCodec.Read(
            ContractEpochLedgerCodec.Write([registration]).AsSpan());
        var candidate = ContractEpochLedgerCodec.Read(
            ContractEpochLedgerCodec.Write(
                [registration, new ContractEpochEvent.Consume("CONTRACT-001")]).AsSpan());

        var delta = ContractEpochLedger.Compare(baseline, candidate);

        Assert.Empty(delta.NewRegistrations);
        Assert.Equal(
            ["CONTRACT-001"],
            delta.EligibleConsumptions.Select(static item => item.PlanId).ToArray());
        Assert.Empty(delta.IneligibleConsumptions);
    }

    [Fact]
    public void CandidateRegistrationCannotBeConsumedInTheSameComparison()
    {
        var registration = Registration("CONTRACT-002");
        var baseline = ContractEpochLedger.Empty;
        var candidate = ContractEpochLedgerCodec.Read(
            ContractEpochLedgerCodec.Write(
                [registration, new ContractEpochEvent.Consume("CONTRACT-002")]).AsSpan());

        var delta = ContractEpochLedger.Compare(baseline, candidate);

        Assert.Single(delta.NewRegistrations);
        Assert.Empty(delta.EligibleConsumptions);
        Assert.Equal(["CONTRACT-002"], delta.IneligibleConsumptions.ToArray());
    }

    [Fact]
    public void DuplicateConsumptionIsRejectedAsReplay()
    {
        var registration = Registration("CONTRACT-003");

        var exception = Assert.Throws<FormatException>(() => ContractEpochLedgerCodec.Read(
            ContractEpochLedgerCodec.Write(
                [
                    registration,
                    new ContractEpochEvent.Consume("CONTRACT-003"),
                    new ContractEpochEvent.Consume("CONTRACT-003"),
                ]).AsSpan()));

        Assert.Contains("consumed more than once", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void BlankLedgerLinesAreNotCanonicalJsonl()
    {
        var bytes = ContractEpochLedgerCodec.Write([Registration("CONTRACT-004")]).Add((byte)'\n');

        var exception = Assert.Throws<FormatException>(() =>
            ContractEpochLedgerCodec.Read(bytes.AsSpan()));

        Assert.Contains("blank", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static ContractEpochEvent.Register Registration(string id) => new(
        id,
        BaselineTree,
        PrePolicy,
        PostPolicy,
        new TransitionPlan.CustodyTransferV1(
            [Path],
            new MachineCustodian(MachineCustodianKind.Loader, "Meta/Loader.cs"),
            Receipt));
}
