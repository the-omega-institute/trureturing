using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.Tests.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed class UtilityRefutationTests
{
    internal const string Claim = "D5/S0/Carrier/Ring.proposed_law";
    internal const string Result = "D5/S0/Carrier/Ring.refuted_law";
    internal const string Refutes = "kind=certified-instance; basis=refutes=gid:" + Claim
        + "; result=" + Result + "; claim=" + Claim;

    [Theory]
    [InlineData("ChangedContent")]
    [InlineData("PreDeposit")]
    [InlineData("FirstFreeze")]
    public void ValidClosedNegationNeedsNoConsumer(string phase)
    {
        var fixture = RefutationFixture();
        Assert.True(Validate(fixture, phase).IsAccepted);
    }

    [Theory]
    [InlineData("ChangedContent")]
    [InlineData("PreDeposit")]
    [InlineData("FirstFreeze")]
    public void PositiveResultRelabeledRefutesIsRejected(string phase)
    {
        var fixture = RefutationFixture();
        fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with
        {
            Refutation = new(Claim, Result, false),
        };
        Assert.Equal(UtilityValidationFailure.RefutationInvalid, Validate(fixture, phase).Failure);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("wrong-claim")]
    [InlineData("wrong-result")]
    [InlineData("non-theorem")]
    [InlineData("foreign-result")]
    [InlineData("excluded-result")]
    [InlineData("ambiguous-result")]
    [InlineData("claim-is-theorem")]
    [InlineData("private-axiom")]
    [InlineData("sorry")]
    [InlineData("self-refutation")]
    public void InvalidOrMissingRefutationEvidenceBlocksEveryPhase(string defect)
    {
        var fixture = RefutationFixture();
        var report = fixture.Reports[RuleFixture.RingPath];
        var text = Refutes;
        report = defect switch
        {
            "missing" => report with { Refutation = null },
            "wrong-claim" => report with { Refutation = new(Result, Result, true) },
            "wrong-result" => report with { Refutation = new(Claim, Claim, true) },
            "non-theorem" => report with { Declarations = [report.Declarations[0], report.Declarations[1] with { Kind = "def" }] },
            "excluded-result" => report with { Declarations = [report.Declarations[0], report.Declarations[1] with { IncludeInStatement = false }] },
            "ambiguous-result" => report with { Declarations = report.Declarations.Add(report.Declarations[1] with { Name = "Other.refuted_law" }) },
            "claim-is-theorem" => report with { Declarations = [report.Declarations[0] with { Kind = "theorem" }, report.Declarations[1]] },
            "private-axiom" => report with { Declarations = [report.Declarations[0], report.Declarations[1] with { Axioms = ["Extra.trusted"] }] },
            "sorry" => report with { Declarations = [report.Declarations[0], report.Declarations[1] with { Axioms = ["sorryAx"] }] },
            _ => report,
        };
        if (defect == "foreign-result") text = text.Replace(Result, "D5/S0/Carrier/ValuesBinding.fixtureValue", StringComparison.Ordinal);
        if (defect == "self-refutation") text = text.Replace(Claim, Result, StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = report;
        foreach (var phase in Enum.GetValues<UtilityValidationPhase>())
            Assert.False(Validate(fixture, phase.ToString(), text).IsAccepted, defect + " " + phase);
    }

    [Theory]
    [InlineData("kind=bounded-enumeration; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law; result=D5/S0/Carrier/Ring.refuted_law")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.refuted_law; result=D5/S0/Carrier/Ring.refuted_law; claim=D5/S0/Carrier/Ring.proposed_law")]
    public void RefutesRequiresBothFieldsAndGidTargetMustBeClaim(string utility)
    {
        Assert.False(Validate(RefutationFixture(), "PreDeposit", utility).IsAccepted);
    }

    [Fact]
    public void AtomCoverageMustNameDesignatedResultAndItsCurrentStatement()
    {
        var fixture = RefutationFixture();
        var text = Refutes.Replace("gid:" + Claim, "atom:" + RuleFixture.FixtureAtomId, StringComparison.Ordinal);
        Assert.True(Validate(fixture, "ChangedContent", text).IsAccepted);
        Assert.True(Validate(fixture, "PreDeposit", text).IsAccepted);
        Assert.Equal(UtilityValidationFailure.RefutesAtomNoCoverage, Validate(fixture, "FirstFreeze", text).Failure);

        var report = fixture.Reports[RuleFixture.RingPath];
        var claimId = CanonicalStatementWriter.DeclarationStatementId(RepoPath.CreateKnown(RuleFixture.RingPath), report.Declarations[0]);
        var resultId = CanonicalStatementWriter.DeclarationStatementId(RepoPath.CreateKnown(RuleFixture.RingPath), report.Declarations[1]);
        var original = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        foreach (var (gid, id, expected) in new[] { (Claim, claimId, false), (Result, claimId, false), (Result, resultId, true) })
        {
            fixture.Files[RuleFixture.FixtureBackfillAtomPath] = original
                .Replace("D5/S0/Carrier/BackfillTarget", gid, StringComparison.Ordinal)
                .Replace("target_statement_id: null", "target_statement_id: " + id, StringComparison.Ordinal);
            Assert.Equal(expected, Validate(fixture, "FirstFreeze", text).IsAccepted);
        }
    }

    [Fact]
    public void RefutationEvidenceRoundTripsWithoutChangingStatementIdentity()
    {
        var fixture = RefutationFixture();
        var context = fixture.Build(RawChangeSet.Create([]));
        var report = LeanAxiomReport.Create(fixture.Reports);
        var loaded = RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(context.Current, report).AsSpan(), context.Current);
        Assert.Equal(fixture.Reports[RuleFixture.RingPath].Refutation, loaded.Files[RepoPath.CreateKnown(RuleFixture.RingPath)].Refutation);
        Assert.Equal(
            CanonicalStatementWriter.DeclarationStatementIds(RepoPath.CreateKnown(RuleFixture.RingPath), fixture.Reports[RuleFixture.RingPath])
                .Select(static item => (item.DeclarationNameKey, item.Kind, item.StatementId.Value)),
            CanonicalStatementWriter.DeclarationStatementIds(RepoPath.CreateKnown(RuleFixture.RingPath), loaded.Files[RepoPath.CreateKnown(RuleFixture.RingPath)])
                .Select(static item => (item.DeclarationNameKey, item.Kind, item.StatementId.Value)));
    }

    [Theory]
    [InlineData("legacy-missing")]
    [InlineData("malformed")]
    [InlineData("stale-binding")]
    public void StrictLoaderDoesNotTurnMissingOrBadEvidenceIntoKnownSuccess(string defect)
    {
        var fixture = RefutationFixture();
        var context = fixture.Build(RawChangeSet.Create([]));
        var root = JsonNode.Parse(RawLeanReportArtifact.Write(context.Current, LeanAxiomReport.Create(fixture.Reports)).AsSpan())!;
        var module = root["modules"]!.AsArray().Single(item => item!["source_path"]!.GetValue<string>() == RuleFixture.RingPath)!;
        if (defect == "legacy-missing") module.AsObject().Remove("utility_refutation");
        else if (defect == "malformed") module["utility_refutation"]!["is_closed_negation"] = "true";
        else module["utility_refutation"]!["claim_gid"] = Result;
        var bytes = StructuredCanonicalWriter.WriteJson(root.ToJsonString());
        if (defect == "legacy-missing")
        {
            var report = RawLeanReportArtifact.Read(bytes.AsSpan(), context.Current);
            Assert.False(UtilityDeclarationValidator.Validate(UtilityValidationPhase.PreDeposit,
                RepoPath.CreateKnown(RuleFixture.RingPath), Refutes, context.Current, () => report).IsAccepted);
        }
        else Assert.Throws<FormatException>(() => RawLeanReportArtifact.Read(bytes.AsSpan(), context.Current));
    }

    [Fact]
    public void StrictLoaderRejectsRefutationEvidenceFromAnEarlierForeignClaimSource()
    {
        const string foreignClaim = "D5/S0/Carrier/ValuesBinding.proposed_law";
        var fixture = RefutationFixture();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(Claim, foreignClaim, StringComparison.Ordinal);
        fixture.Files[RuleFixture.ValuesBindingPath] += "def proposed_law : Prop := False\n";
        fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with
        {
            Refutation = new(foreignClaim, Result, true),
        };
        var before = fixture.Build(RawChangeSet.Create([])).Current;
        var root = JsonNode.Parse(RawLeanReportArtifact.Write(before, LeanAxiomReport.Create(fixture.Reports)).AsSpan())!;
        fixture.Files[RuleFixture.ValuesBindingPath] = fixture.Files[RuleFixture.ValuesBindingPath].Replace("False", "True", StringComparison.Ordinal);
        var current = fixture.Build(RawChangeSet.Create([])).Current;
        var claimModule = root["modules"]!.AsArray().Single(item => item!["source_path"]!.GetValue<string>() == RuleFixture.ValuesBindingPath)!;
        claimModule["source_sha256"] = "sha256:" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            current.Files[RepoPath.CreateKnown(RuleFixture.ValuesBindingPath)].RawBytes.AsSpan()));

        Assert.Throws<FormatException>(() => RawLeanReportArtifact.Read(
            StructuredCanonicalWriter.WriteJson(root.ToJsonString()).AsSpan(), current));
    }

    internal static RuleFixture RefutationFixture()
    {
        var fixture = OrdinaryInstanceAdmissionTests.InstanceFixture(Refutes);
        fixture.Reports[RuleFixture.RingPath] = new([], [
            new("proposed_law", "def", "Prop := False", []),
            new("refuted_law", "theorem", "Not proposed_law", []),
        ]) { Refutation = new(Claim, Result, true) };
        return fixture;
    }

    private static UtilityValidationResult Validate(RuleFixture fixture, string phase, string utility = Refutes)
    {
        var context = fixture.BuildForRuleCompatibility(RawChangeSet.Create([]));
        return UtilityDeclarationValidator.Validate(Enum.Parse<UtilityValidationPhase>(phase),
            RepoPath.CreateKnown(RuleFixture.RingPath), utility, context.Current, () => context.Lean.Report);
    }
}
