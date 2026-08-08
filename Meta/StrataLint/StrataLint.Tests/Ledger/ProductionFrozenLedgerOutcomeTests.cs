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

        AssertSl008Rejection(
            outcome,
            "candidate frozen ledger does not retain every baseline path byte-for-byte");
    }

    [Fact]
    public void ProductionValidatorRejectsMutatingABaselineAcceptedEventFile()
    {
        var fixture = CreateFrozenValidatorFixture();
        var path = fixture.BaselineFiles.Keys.First(
            FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        fixture.CurrentFiles[path] += " ";

        var outcome = Validate(fixture, CreateGateway(fixture));

        AssertSl008Rejection(
            outcome,
            "candidate frozen ledger does not retain every baseline path byte-for-byte");
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
                throw new InvalidOperationException("synthetic invalid reference");
            }

            return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
        });

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "frozen ledger Git references are invalid: synthetic invalid reference");
        Assert.Equal(failingCall, gateway.FrozenReferenceValidationCount);
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
}
