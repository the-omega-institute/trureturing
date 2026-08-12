using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void ProductionValidatorRejectsDeletingABaselineAcceptedEventFile()
    {
        var fixture = CreateFrozenValidatorFixture();
        var path = fixture.BaselineFiles.Keys.First(
            FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        fixture.CurrentFiles.Remove(path);

        var outcome = Validate(fixture, CreateGateway(fixture));

        var diagnostic = AssertSl008Rejection(
            outcome,
            "candidate content-addressed ledger does not retain protected baseline file byte-for-byte",
            path);
        Assert.DoesNotContain(FrozenLedgerChangeClassifier.LedgerPath, diagnostic.Render(), StringComparison.Ordinal);
    }

    // 冻结账本验证器**不是**只比文件字节:它还要拿账本去佐证 baselineDag 里的 Closed 模块。
    // 所以账本旧侧不能单独迁到 fork point —— 账本取一棵树、其佐证目标取另一棵,就会把 dev
    // 在分叉后闭合的模块报成「Closed module ... has no Freeze attestation」(#1166 实测)。
    // 这条守卫钉住那个刻意的选择:传入一个与 baseline 不同的 fork point,判词必须不变。
    // 若有人把账本旧侧改读 fork point 而不同时把 Lean report 与 DAG 一并迁过去,本测试转红。
    [Fact]
    public void FrozenLedgerOldSideIgnoresTheForkPointUntilItsLeanAndDagMoveTogether()
    {
        var fixture = CreateFrozenValidatorFixture();
        var dropped = fixture.BaselineFiles.Keys.First(
            FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        var forkPointFiles = new Dictionary<string, string>(
            fixture.BaselineFiles,
            StringComparer.Ordinal);
        forkPointFiles.Remove(dropped);

        var current = BuildState(fixture.CurrentFiles, fixture.CurrentReports);
        var baseline = BuildState(fixture.BaselineFiles, fixture.BaselineReports);
        var outcome = ProductionFrozenLedgerValidator.Validate(
            current.Snapshot,
            baseline.Snapshot,
            current.Lean,
            baseline.Lean,
            current.Dag,
            baseline.Dag,
            CreateGateway(fixture),
            frozenEvidenceRepository: null,
            forkPoint: BuildState(forkPointFiles, fixture.BaselineReports).Snapshot);

        Assert.True(
            outcome is null,
            "fork point 不得改变冻结账本判词,除非其 Lean report 与 DAG 一并迁移。实际: "
            + (outcome is AdmissionOutcome.RuleRejected rejected
                ? string.Join(" | ", rejected.Diagnostics.Select(static item => item.Message))
                : outcome?.ToString()));
    }

    [Fact]
    public void ProductionValidatorRejectsMutatingABaselineAcceptedEventFile()
    {
        var fixture = CreateFrozenValidatorFixture();
        var path = fixture.BaselineFiles.Keys.First(
            FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        fixture.CurrentFiles[path] += " ";

        var outcome = Validate(fixture, CreateGateway(fixture));

        var diagnostic = AssertSl008Rejection(
            outcome,
            "candidate content-addressed ledger does not retain protected baseline file byte-for-byte",
            path);
        Assert.DoesNotContain(FrozenLedgerChangeClassifier.LedgerPath, diagnostic.Render(), StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionValidatorReportsTheFirstPathAndCountForMultipleUnretainedAcceptedFiles()
    {
        var fixture = CreateFrozenValidatorFixture();
        AppendCurrentReattestation(fixture);
        var acceptedPaths = fixture.CurrentFiles.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
            .OrderBy(static path => path, StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(3, acceptedPaths.Length);
        fixture.BaselineFiles.Clear();
        foreach (var pair in fixture.CurrentFiles)
        {
            fixture.BaselineFiles[pair.Key] = pair.Value;
        }
        var originalPath = acceptedPaths[0];
        fixture.CurrentFiles.Remove(acceptedPaths[0]);
        fixture.CurrentFiles[acceptedPaths[1]] += " ";

        var outcome = Validate(fixture, CreateGateway(fixture));

        var diagnostic = AssertSl008Rejection(
            outcome,
            "candidate content-addressed ledger does not retain protected baseline file byte-for-byte (2 baseline accepted files are missing or mutated)",
            originalPath);
        Assert.DoesNotContain(FrozenLedgerChangeClassifier.LedgerPath, diagnostic.Render(), StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionValidatorAcceptsARevocationBackedByAProtectedTypedReceipt()
    {
        var fixture = CreateRevocationValidatorFixture(includeReceiptInBaseline: true);

        var rejection = Validate(fixture, CreateGateway(fixture));

        Assert.True(
            rejection is null,
            rejection is AdmissionOutcome.RuleRejected rejected
                ? string.Join(" | ", rejected.Diagnostics.Select(static item => item.Message))
                : rejection?.ToString());
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void ProductionValidatorRejectsInvalidGitReferencesAtEitherGatewayCall(int failingCall)
    {
        var fixture = CreateFrozenValidatorFixture();
        var calls = 0;
        var gateway = CreateGateway(fixture, references =>
        {
            calls++;
            if (calls == failingCall)
            {
                throw new FrozenReferenceRejectionException(
                    FrozenReferenceRejectionKind.InvalidReference,
                    "synthetic invalid reference");
            }

            return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
        });

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "frozen ledger Git references are invalid: synthetic invalid reference");
        Assert.Equal(failingCall, gateway.FrozenReferenceValidationCount);
        Assert.Equal(1, CheckExitCode(outcome!));
    }

    [Fact]
    public void ProductionValidatorMapsGitInfrastructureFailuresToExitTwo()
    {
        foreach (var kind in new[]
        {
            GitCommandFailureKind.ExecutableNotFound,
            GitCommandFailureKind.Timeout,
            GitCommandFailureKind.Io,
        })
        {
            var fixture = CreateFrozenValidatorFixture();
            var failure = new GitCommandFailure(
                kind,
                "git",
                ImmutableArray.Create("cat-file", "-t", new string('f', 40)),
                null,
                kind is GitCommandFailureKind.ExecutableNotFound ? 2 : null,
                string.Empty,
                $"synthetic {kind} failure");
            var gateway = CreateGateway(
                fixture,
                _ => throw new GitInfrastructureException(failure));

            var outcome = Validate(fixture, gateway);

            var infrastructure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
            Assert.Contains("frozen ledger Git infrastructure failed", infrastructure.Message, StringComparison.Ordinal);
            Assert.Contains(failure.Render(), infrastructure.Message, StringComparison.Ordinal);
            Assert.Equal(2, CheckExitCode(infrastructure));
            Assert.Equal(1, gateway.FrozenReferenceValidationCount);
        }
    }

    [Fact]
    public void ProductionValidatorRejectsInvalidProtectedLedgerMaterial()
    {
        var fixture = CreateFrozenValidatorFixture();
        fixture.BaselineFiles.Remove("lean-toolchain");
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "protected baseline ledger material is invalid: Frozen environment source files are missing.");
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorRejectsInvalidProtectedLedgerHistory()
    {
        var fixture = CreateFrozenValidatorFixture();
        fixture.BaselineFiles.Remove("D5/S0/Carrier/A.lean");
        fixture.BaselineReports.Remove("D5/S0/Carrier/A.lean");
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "protected baseline ledger is invalid: Active frozen history contains modules outside the current Closed catalog: D5/S0/Carrier/A.lean");
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorRejectsMissingProtectedRevocationReceiptMaterial()
    {
        var fixture = CreateRevocationValidatorFixture(includeReceiptInBaseline: false);
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            $"candidate revocation receipt material is invalid: Revocation receipt {fixture.ReceiptOid} is not a blob in the protected baseline snapshot.");
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorRejectsInvalidCandidateLedgerMaterial()
    {
        var fixture = CreateFrozenValidatorFixture();
        fixture.CurrentFiles.Remove("lean-toolchain");
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "candidate ledger material is invalid: Frozen environment source files are missing.");
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorRejectsInvalidCandidateLedgerHistory()
    {
        var fixture = CreateFrozenValidatorFixture();
        fixture.CurrentFiles.Remove("D5/S0/Carrier/A.lean");
        fixture.CurrentReports.Remove("D5/S0/Carrier/A.lean");
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "candidate ledger is invalid: Active frozen view does not exactly match the current Closed module identities.");
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorValidatesBaselineThenCandidateReferencesAndAccepts()
    {
        var fixture = CreateFrozenValidatorFixture();
        AppendCurrentReattestation(fixture);
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        Assert.Null(outcome);
        Assert.Collection(
            gateway.FrozenReferenceValidations,
            references => Assert.Single(references.Inputs),
            references => Assert.Equal(2, references.Inputs.Length));
    }

    private static int CheckExitCode(AdmissionOutcome outcome) =>
        CliApplication.Run(["check"], new StubCliEnvironment(outcome), new BufferedConsole());
}
