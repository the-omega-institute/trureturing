namespace StrataLint.Cli;

internal static class PapergenCommand
{
    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
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
            return PaperRecipeValidator.Validate(repositoryRoot, id) switch
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
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"PAPERGEN_VALIDATE_INFRASTRUCTURE id={id} {exception.Message}\n");
        }
    }
}
