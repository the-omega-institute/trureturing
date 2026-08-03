using System.Text;
namespace StrataLint.Cli;

internal static class PapergenCommand
{
    internal static ExplicitCommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || !string.Equals(arguments[0], "validate", StringComparison.Ordinal))
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                "USAGE: StrataLint papergen validate PAPER_ID\n");
        }

        var id = arguments[1];
        try
        {
            return PaperRecipeValidator.Validate(repositoryRoot, repository, leanReportSource, id) switch
            {
                PaperRecipeValidationOutcome.Valid valid => new ExplicitCommandResult(
                    0,
                    $"PAPERGEN_VALIDATE_OK id={valid.Recipe.Id} gid=D5/P/{valid.Recipe.Id} "
                    + $"recipe_sha256={valid.RecipeSha256} "
                    + $"decls={valid.Recipe.Declarations.Length} "
                    + $"blueprint={valid.Recipe.Blueprint.Length} "
                    + $"evidence={valid.Recipe.Evidence.Length} "
                    + $"narrative_order={valid.Recipe.NarrativeOrder.Length} "
                    + $"venue={valid.Recipe.Venue}\n",
                    string.Empty),
                PaperRecipeValidationOutcome.Invalid invalid => new ExplicitCommandResult(
                    1,
                    string.Empty,
                    $"PAPERGEN_VALIDATE_INVALID id={id} {invalid.Message}\n"),
                _ => throw new InvalidOperationException("unknown paper recipe validation outcome"),
            };
        }
        // The marker types say a fault came from the raw Lean report or from reading the
        // repository -- both infrastructure. They are caught as themselves rather than unwrapped,
        // because unwrapping hands back the very exception types a ledger verdict uses, and the
        // distinction is then lost at exactly the boundary that needs it. The plain types remain
        // for faults raised before preparation is reached.
        catch (Exception exception) when (exception
            is DagLedgerCommandPreparation.LeanReportUnusableException
            or DagLedgerCommandPreparation.RepositoryUnavailableException
            or IOException or UnauthorizedAccessException or FormatException or DecoderFallbackException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"PAPERGEN_VALIDATE_INFRASTRUCTURE id={id} {(exception.InnerException ?? exception).Message}\n");
        }
    }
}
