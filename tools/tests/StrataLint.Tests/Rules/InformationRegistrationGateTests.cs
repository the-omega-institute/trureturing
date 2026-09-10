using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.Tests.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed class InformationRegistrationGateTests
{
    private const string Ignored = "IE-C048 RealizationIgnoredByLaw key=Root/Catalog/T law_arena=A signature=A.signature domain=all reason=missing_witness";
    private const string Unused = "IE-C049 UnusedPrimitiveInBundle key=Root/Catalog/T signature=A.signature primitive=null support=null";

    [Theory]
    [InlineData(Ignored)]
    [InlineData(Unused)]
    public void ChangedUnfrozenRegistrationIsRejected(string message)
    {
        var fixture = Fixture(message);
        fixture.Files[RuleFixture.RingPath] += "\n-- candidate byte change\n";
        Assert.Contains(Evaluate(fixture, RuleFixture.RingPath), d => d.Message == message && d.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void NewRegistrationIsRejectedWithoutAStatePin()
    {
        var fixture = Fixture(Ignored);
        fixture.Baseline.Remove(RuleFixture.RingPath);
        Assert.Contains(Evaluate(fixture, RuleFixture.RingPath), d => d.Message == Ignored);
    }

    [Fact]
    public void UnchangedUnfrozenRegistrationIsOutsideDelta()
    {
        var fixture = Fixture(Ignored);
        Assert.DoesNotContain(Evaluate(fixture, RuleFixture.RingPath), d => d.Message.StartsWith("IE-C", StringComparison.Ordinal));
    }

    [Fact]
    public void JudgeOnlyDeltaDoesNotRejectHistoricalRegistration()
    {
        var fixture = Fixture(Ignored);
        const string judge = "tools/StrataLint.Engine/Rules/Fixture.cs";
        fixture.Files[judge] = "// changed judge\n";
        Assert.DoesNotContain(Evaluate(fixture, judge), d => d.Message.StartsWith("IE-C", StringComparison.Ordinal));
    }

    [Fact]
    public void ProtectedBaseFrozenRegistrationIsOutsideDelta()
    {
        var fixture = Fixture(Ignored);
        AddExistingFrozenState(fixture);
        fixture.Files[RuleFixture.RingPath] += "\n-- SL-008 owns frozen byte changes\n";
        Assert.DoesNotContain(Evaluate(fixture, RuleFixture.RingPath), d => d.Message.StartsWith("IE-C", StringComparison.Ordinal));
    }

    [Fact]
    public void CandidatePinDoesNotExemptChangedRegistration()
    {
        var fixture = Fixture(Ignored);
        var pin = AddExistingFrozenState(fixture);
        fixture.Baseline.Remove(pin);
        fixture.Files[RuleFixture.RingPath] += "\n-- changed\n";
        Assert.Contains(Evaluate(fixture, RuleFixture.RingPath), d => d.Message == Ignored);
    }

    [Fact]
    public void CompleteWitnessEvidencePasses()
    {
        var fixture = Fixture();
        fixture.Files[RuleFixture.RingPath] += "\n-- changed\n";
        Assert.DoesNotContain(Evaluate(fixture, RuleFixture.RingPath), d => d.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void MissingReportEvidenceFailsClosedOnlyInDelta()
    {
        var fixture = Fixture();
        fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with { InformationRegistrationErrors = null };
        Assert.DoesNotContain(Evaluate(fixture, RuleFixture.RingPath), d => d.AdmissionEffect == AdmissionEffect.Block);
        fixture.Files[RuleFixture.RingPath] += "\n-- changed\n";
        Assert.Contains(Evaluate(fixture, RuleFixture.RingPath), d => d.Message.Contains("INFORMATION-REGISTRATION-EVIDENCE-MISSING", StringComparison.Ordinal));
    }

    [Fact]
    public void RegistrationDiagnosticsSurviveSourceBoundReportRoundTrip()
    {
        var fixture = Fixture(Ignored, Unused);
        var context = fixture.Build();
        var bytes = RawLeanReportArtifact.Write(context.Current, context.Lean.Report);
        var loaded = RawLeanReportArtifact.Read(bytes.AsSpan(), context.Current);
        Assert.Equal(new[] { Ignored, Unused }, loaded.Files[RepoPath.CreateKnown(RuleFixture.RingPath)].InformationRegistrationErrors);
    }

    private static RuleFixture Fixture(params string[] messages)
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(fixture.Files[RuleFixture.RingPath], "none");
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with { InformationRegistrationErrors = messages.ToImmutableArray() };
        return fixture;
    }

    private static IReadOnlyList<Diagnostic> Evaluate(RuleFixture fixture, string path) =>
        RuleCatalog.Default.EvaluateSingle(UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds([(path, RawChangeKind.Modified)]))).Diagnostics;
}
