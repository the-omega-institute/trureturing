using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ProductionValidatorRejectsWhenEitherLedgerIsMissing(bool removeBaselineLedger)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = removeBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files.Remove(FrozenLedgerChangeClassifier.LedgerPath);
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "frozen ledger is missing from current or protected baseline");
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [InlineData(true, "protected baseline ledger syntax is invalid: Frozen ledger contains a blank or CR-terminated line.")]
    [InlineData(false, "candidate ledger syntax is invalid: Frozen ledger contains a blank or CR-terminated line.")]
    public void ProductionValidatorRejectsInvalidLedgerSyntax(
        bool corruptBaselineLedger,
        string expectedMessage)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = corruptBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files[FrozenLedgerChangeClassifier.LedgerPath] = "\n";
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(outcome, expectedMessage);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [InlineData(true, "protected baseline ledger fields are invalid: event envelope has unknown, missing, or duplicate fields.")]
    [InlineData(false, "candidate ledger fields are invalid: event envelope has unknown, missing, or duplicate fields.")]
    public void ProductionValidatorRejectsInvalidLedgerFields(
        bool corruptBaselineLedger,
        string expectedMessage)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = corruptBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files[FrozenLedgerChangeClassifier.LedgerPath] = "{}\n";
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(outcome, expectedMessage);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }
}
