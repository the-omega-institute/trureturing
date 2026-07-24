using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class RouteCommand
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 1)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint route MANIFEST|-\n");
            }

            var registry = RegistryLoader.LoadRepository(repositoryRoot);
            var manifestBytes = arguments[0] == "-"
                ? ReadStandardInput()
                : ReadRepositoryFile(repositoryRoot, arguments[0]);
            var manifestOutcome = ManifestLoader.Load(manifestBytes);
            if (manifestOutcome is ManifestLoadOutcome.InfrastructureFailure manifestFailure)
            {
                return new CommandResult(
                    false,
                    string.Empty,
                    $"INFRASTRUCTURE_FAILURE {manifestFailure.Message}\n");
            }

            var manifest = ((ManifestLoadOutcome.Loaded)manifestOutcome).Syntax;
            return RouteEngine.Route(registry.Policy, manifest) switch
            {
                RouteOutcome.Routed routed => new CommandResult(
                    true,
                    JsonSerializer.Serialize(
                        new
                        {
                            gid = routed.Result.Gid.Value,
                            path = routed.Result.Path.Value,
                            stratum = routed.Result.Stratum?.ToString(),
                            skeleton = routed.Result.Skeleton,
                        },
                        JsonOptions) + "\n",
                    string.Empty),
                RouteOutcome.Rejected rejected => new CommandResult(
                    false,
                    string.Empty,
                    $"{rejected.RuleId.Value} route: {rejected.Message}\n"),
            };
        }
        catch (Exception exception)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE {exception.Message}\n");
        }
    }

    private static byte[] ReadRepositoryFile(string repositoryRoot, string relativePath)
    {
        if (!RepoPath.TryCreate(relativePath, out var path))
        {
            throw new InvalidOperationException("manifest path must be repository-relative");
        }

        return File.ReadAllBytes(Path.Combine(repositoryRoot, path.Value));
    }

    private static byte[] ReadStandardInput()
    {
        using var memory = new MemoryStream();
        Console.OpenStandardInput().CopyTo(memory);
        return memory.ToArray();
    }
}
