using System.Text;
using System.Text.Json;

namespace StrataLint.Cli;

internal static class LeanCacheWarmCommand
{
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, IDirectoryCloner cloner)
    {
        if (!LeanCacheEnsureCommand.TryParse(repositoryRoot, arguments, false, out var root, out _))
            return new(false, string.Empty, "USAGE: StrataLint worktree warm-cache [--path DIR]\n");
        var output = new StringBuilder();
        string? stage = null;
        try
        {
            root = LeanCacheGuard.PhysicalPath(root);
            RequireMainDev(root, runner);
            if (!OperatingSystem.IsMacOS() || !File.Exists("/usr/bin/sandbox-exec"))
                throw new PlatformNotSupportedException("Shared cache warming requires the verified macOS reader guard.");
            var pins = ReadPins(root);
            var policy = LeanProcessPolicy.Create(root, pins, runner);
            using var warmer = LeanCacheWriterGuard.TryAcquire(policy.SharedRoot, policy.LockDirectory)
                ?? throw new InvalidOperationException("shared cache warmer is busy");
            using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"), policy.LockDirectory)
                ?? throw new InvalidOperationException("private main .lake writer guard is busy");
            RequireMainDev(root, runner);
            LeanCacheProvisioner.RequirePrivateLake(root);
            var pull = runner.Run("git", ["pull", "--ff-only", "origin", "dev"], root,
                LeanCacheProvisioner.DependencyFetchBudget);
            output.Append(Encoding.UTF8.GetString(pull.StandardOutput));
            LeanCacheProvisioner.RequireSuccess(pull, "git pull --ff-only origin dev");
            RequireMainDev(root, runner);
            var head = LeanProcessPolicy.Git(root, runner, "rev-parse", "HEAD");
            pins = ReadPins(root);
            policy = LeanProcessPolicy.Create(root, pins, runner);
            output.Append(LeanCacheProvisioner.Ensure(policy, pins, guard));
            stage = Path.Combine(root, ".lake", "cache-stage-" + Path.GetRandomFileName());
            if (Directory.Exists(policy.SharedCache))
                LeanArtifactPublisher.CopyDetached(policy.SharedCache, stage, root, runner, cloner);
            else
                Directory.CreateDirectory(stage);
            var writer = policy.StageWriter(stage);
            var built = writer.Run(policy.LakeExecutable, ["build"], root, LeanCacheProvisioner.LeanCommandBudget);
            output.Append(Encoding.UTF8.GetString(built.StandardOutput));
            LeanCacheProvisioner.RequireSuccess(built, "Lake warming build");
            RequireMainDev(root, runner);
            if (head != LeanProcessPolicy.Git(root, runner, "rev-parse", "HEAD") || !pins.HasSameBytes(ReadPins(root)))
                throw new InvalidOperationException("main checkout changed during warming");
            warmer.RequireOwnershipOf(policy.SharedRoot);
            var counts = LeanArtifactPublisher.Publish(stage, policy.SharedCache,
                Path.GetDirectoryName(policy.SharedRoot)!, root, runner, cloner);
            output.Append("LEAN_DONOR_WARM " + JsonSerializer.Serialize(new
            {
                status = "warmed", cache = policy.SharedCache, artifacts = counts.Artifacts, mappings = counts.Mappings,
            }) + "\n");
            return new(true, output.ToString(), string.Empty);
        }
        catch (Exception exception)
        {
            return new(false, output.ToString(), "LEAN_DONOR_WARM " + JsonSerializer.Serialize(new
            {
                status = "failed", reason = exception.Message,
            }) + "\n");
        }
        finally
        {
            if (stage is not null && Directory.Exists(stage)) Directory.Delete(stage, recursive: true);
        }
    }

    private static LeanPinSet ReadPins(string root) => LeanPinSet.TryReadWorktree(root, out var reason)
        ?? throw new InvalidOperationException(reason);

    private static void RequireMainDev(string root, IWorktreeProcessRunner runner)
    {
        var common = LeanProcessPolicy.Git(root, runner, "rev-parse", "--path-format=absolute", "--git-common-dir");
        var git = LeanProcessPolicy.Git(root, runner, "rev-parse", "--absolute-git-dir");
        var top = LeanProcessPolicy.Git(root, runner, "rev-parse", "--show-toplevel");
        if (LeanCacheGuard.PhysicalPath(common) != LeanCacheGuard.PhysicalPath(git)
            || LeanCacheGuard.PhysicalPath(top) != root)
            throw new InvalidOperationException("only the physical main checkout may warm the shared cache");
        if (LeanProcessPolicy.Git(root, runner, "symbolic-ref", "--short", "HEAD") != "dev")
            throw new InvalidOperationException("main warming requires branch dev");
        if (LeanProcessPolicy.Git(root, runner, "status", "--porcelain", "--untracked-files=normal").Length != 0)
            throw new InvalidOperationException("main warming requires a clean checkout");
    }
}
