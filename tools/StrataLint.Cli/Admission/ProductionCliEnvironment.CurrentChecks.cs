using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    private ExplicitCommandResult ExecuteCommonCurrent(string round, RepositorySnapshot snapshot,
        ValidatedPolicy policy, AcceptedLeanClosure lean, LeanAxiomReport report, string[]? selectedIds = null)
    {
        using var trace = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        var build = CommonExecutionEvidence.ValidateBuild(repositoryRoot, round);
        var checks = CommonExecutionEvidence.BeginChecks(repositoryRoot, "current", build, trace, selectedIds);
        var assembly = typeof(DocumentAssembly).Assembly;
        CheckWork Scribe(string id, string[] arguments, bool capability = false)
        {
            using var stdout = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
            using var stderr = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
            var exit = ScribeCli.Run(assembly, arguments, repositoryRoot, stdout, stderr, report);
            VerifiedScribeEmissions? emissions = null;
            if (exit == 0 && capability)
            {
                try { emissions = ProductionScribeEmissionVerifier.VerifyMaterialized(assembly, repositoryRoot, report, null, null); }
                catch (InvalidOperationException exception) { stderr.WriteLine(exception.Message); exit = 1; }
            }
            return new([new(id, exit, stdout.ToString() + stderr)], emissions?.WriteMaterial());
        }
        // The registered projection unit is the sole projection verification here.
        // ScribeEmitter issues the actual emission capability; shell status cannot issue it.
        if (checks.Ids.Contains("scribe-projections")) checks.Run("scribe-projections", () => Scribe("scribe-projections",
            ["projections", "--check", "--report", CommonExecutionEvidence.ReportPath]));
        if (checks.Ids.Contains("scribe-describe")) checks.Run("scribe-describe", () => Scribe("scribe-describe", ["describe-report", "--check"], capability: true));
        if (checks.Ids.Contains("scribe-markdown")) checks.Run("scribe-markdown", () =>
        {
            var declaration = CommonExecutionEvidence.ReadCheckManifest(snapshot).Single(check => check.Id == "scribe-markdown");
            var paths = EngineeringProjectRegistry.ExpandInputs(snapshot.Files.Keys.Select(path => path.Value), declaration.PathInventory, [], declaration.Id);
            File.WriteAllText(Path.Combine(repositoryRoot, CommonExecutionEvidence.ScribeMarkdownPaths), string.Join("\n", paths) + "\n");
            return Scribe("scribe-markdown", ["markdown-check", "--report", CommonExecutionEvidence.ReportPath,
                "--paths-from", Path.Combine(repositoryRoot, CommonExecutionEvidence.ScribeMarkdownPaths)]);
        });
        if (checks.Ids.Contains("filemap")) checks.Run("filemap", () =>
        {
            var result = FileMapConform([]);
            return new([new("filemap", result.ExitCode, result.Output + result.Error)]);
        });
        if (!checks.Ids.Any(id => id.StartsWith("SL-", StringComparison.Ordinal)))
        {
            _ = checks.Seal();
            return new(0, trace + System.Text.Json.JsonSerializer.Serialize(new { accepted_units = checks.Ids }) + "\n", "");
        }
        var combined = checks.ExecuteCurrentPredicates(policy, lean);
        var rendered = RenderStage(combined);
        if (rendered.ExitCode != 0) return new(rendered.ExitCode, trace + rendered.Output, rendered.Error);
        if ((selectedIds is null || CommonExecutionEvidence.ReadCheckManifest(snapshot).Where(check => check.Id.StartsWith("SL-", StringComparison.Ordinal)).All(check => checks.Ids.Contains(check.Id)))
            && RepositoryCanonicalizer.Validate(snapshot, policy) is CanonicalizationOutcome.InfrastructureFailure failure)
            return new(2, trace + RenderStage(combined).Output, "INFRASTRUCTURE_FAILURE " + failure.Message + "\n");
        _ = checks.Seal();
        var accepted = RenderStage(combined);
        return new(accepted.ExitCode, trace + accepted.Output, accepted.Error);
    }
}
