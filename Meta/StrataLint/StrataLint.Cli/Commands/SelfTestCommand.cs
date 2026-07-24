using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class SelfTestCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint selftest\n");
            }

            var registry = RegistryLoader.LoadRepository(repositoryRoot);
            var probe = new ManifestSyntax(
                "D5",
                "F",
                "Carrier",
                "Probe",
                "G",
                string.Empty,
                "lean",
                string.Empty);
            var route = RouteEngine.Route(registry.Policy, probe);
            if (route is not RouteOutcome.Routed routed
                || routed.Result.Gid.Value != "D5/S0/Carrier/Probe"
                || routed.Result.Path.Value != "D5/S0/Carrier/Probe.lean"
                || RuleCatalog.Default.Descriptors.Length != 23)
            {
                return new CommandResult(false, string.Empty, "SELFTEST FAIL invariant mismatch\n");
            }

            var rules = string.Join(
                ",",
                RuleCatalog.Default.Descriptors.Select(static item => item.Id.Value));
            var deferred = string.Join(
                ",",
                RuleCatalog.Default.Descriptors
                    .Where(static item => item.Lifecycle is RuleLifecycle.Deferred)
                    .Select(static item => $"{item.Id.Value}:{item.DeferredCase?.Value}"));
            var output = "SELFTEST PASS\n"
                + $"CANONICAL_REGISTRY {registry.Policy.RegistrySha256}\n"
                + $"CANONICAL_DOMAINS {registry.Policy.DomainsSha256}\n"
                + $"RULES {rules}\n"
                + $"DEFERRED {deferred}\n";
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"SELFTEST FAIL {exception.Message}\n");
        }
    }
}
