using System.Text.Json;

namespace StrataLint.Cli;

internal static class LeanCacheEnsureCommand
{
    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR]";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner) =>
        Run(repositoryRoot, arguments, runner, new ApfsDirectoryCloner());

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
        if (!TryParseWorktreeRoot(repositoryRoot, arguments, out var root))
        {
            return new CommandResult(false, string.Empty, Usage + "\n");
        }

        var lake = Path.Combine(root, ".lake");
        try
        {
            if (IsSymlink(lake)) return RefusedSymlink(lake);
            if (Directory.Exists(lake))
            {
                return SuccessReceipt("present", root, donor: null, method: "none", reason: null);
            }

            if (File.Exists(lake))
            {
                return ColdReceipt(root, donor: null, ".lake exists but is not a directory");
            }

            var pins = LeanPinSet.TryReadWorktree(root, out var pinReason);
            if (pins is null)
            {
                return ColdReceipt(root, donor: null, pinReason ?? "Lean pin files are unavailable");
            }

            var selection = GitWorktreeInventory.SelectDonor(root, pins, runner);
            try
            {
                var provisioned = LeanCacheProvisioner.Provision(selection, root, runner, cloner);
                var reason = JoinReasons(selection.Notice, provisioned.Warning);
                return SuccessReceipt(
                    provisioned.Strategy == "cloned" ? "seeded" : "fetched",
                    root,
                    selection.Donor,
                    provisioned.Method,
                    reason);
            }
            catch (Exception exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(lake);
                return ColdReceipt(root, selection.Donor, JoinReasons(selection.Notice, exception.Message));
            }
        }
        catch (Exception exception)
        {
            return ColdReceipt(root, donor: null, exception.Message);
        }
    }

    private static CommandResult SuccessReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? reason) =>
        new(
            true,
            RenderReceipt(status, worktree, donor, method, reason),
            string.Empty);

    private static CommandResult ColdReceipt(
        string worktree,
        string? donor,
        string reason) =>
        SuccessReceipt("cold", worktree, donor, "none", reason);

    private static CommandResult RefusedSymlink(string lake) =>
        new(
            false,
            string.Empty,
            RenderReceipt(
                "refused",
                Path.GetDirectoryName(lake) ?? lake,
                donor: null,
                method: "none",
                reason: ".lake is a symlink; shared Lean caches are forbidden"));

    private static bool TryParseWorktreeRoot(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        out string root)
    {
        var path = repositoryRoot;
        if (arguments.Count != 0)
        {
            if (arguments.Count != 2
                || !string.Equals(arguments[0], "--path", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[1]))
            {
                root = string.Empty;
                return false;
            }

            path = arguments[1];
        }

        root = Path.GetFullPath(path);
        return true;
    }

    private static string RenderReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? reason) =>
        "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status,
            worktree,
            donor,
            method,
            reason,
        }) + "\n";

    private static string JoinReasons(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second ?? "unknown provisioning failure";
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }

    private static bool IsSymlink(string path) =>
        (Directory.Exists(path) || File.Exists(path))
        && File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint);
}
