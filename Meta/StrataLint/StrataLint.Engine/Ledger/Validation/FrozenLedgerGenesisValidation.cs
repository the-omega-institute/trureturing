using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    public static FrozenLedgerValidationOutcome ValidateGenesis(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        try
        {
            if (syntax.Lines.Length == 0)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            var first = syntax.Lines[0].Value;
            if (RequiredString(first, "event_type") != "Genesis")
            {
                throw new FormatException("The first event must be Genesis.");
            }

            _ = ParseGenesis(first.GetProperty("payload"), catalog);
            if (syntax.Lines.Skip(1).Any(line =>
                RequiredString(line.Value, "event_type") != "Freeze"))
            {
                throw new FormatException("Genesis generation may contain only Genesis and Freeze events.");
            }

            return ValidateHistory(syntax, catalog, trustedReferences);
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException)
        {
            return new FrozenLedgerValidationOutcome.Rejected(exception.Message);
        }
    }
}
