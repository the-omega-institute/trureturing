using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class LeanMissingPackagesProvisioner
{
    internal static bool PackagesAreAbsent(string lake)
    {
        try
        {
            _ = File.GetAttributes(Path.Combine(lake, "packages"));
            return false;
        }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        {
            return true;
        }
    }

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        ILeanCacheStateProbe stateProbe,
        Action<TimeSpan>? wait = null)
    {
        var lake = Path.Combine(worktreeRoot, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        LeanCacheProvisioner.VerifyPrivateDirectory(lake);
        if (selection.Donor is null)
            throw new InvalidOperationException(selection.Notice ?? "packages donor is unavailable");

        var donorLake = Path.Combine(selection.Donor, ".lake");
        var source = Path.Combine(donorLake, "packages");
        var target = Path.Combine(lake, "packages");
        var staged = Path.Combine(lake, "packages.stage-" + Path.GetRandomFileName());
        using var guard = selection.TakeGuard() ?? LeanCacheGuard.TryAcquireShared(donorLake);
        if (guard is null)
            throw new InvalidOperationException("donor cache guard is busy");

        RequireAbsent(target, stateProbe);
        if (!LeanCacheStamp.Matches(lake, pins, out var stampReason))
            throw new InvalidOperationException(stampReason ?? "target cache stamp is not compatible");
        var stamp = File.ReadAllBytes(LeanCacheStamp.PathFor(lake));
        ValidateDonor(selection.Donor, donorLake, pins, runner, stateProbe);

        var clonefile = ClonefileReceipt.NotRun;
        try
        {
            var clone = LeanCacheProvisioner.CloneWithRetry(
                source,
                staged,
                cloner,
                LeanCacheProvisioner.RemovePartial,
                wait ?? LeanCacheProvisioner.WaitForRetry,
                out clonefile);
            if (!clone.Succeeded)
                throw new InvalidOperationException($"donor packages clonefile seeding failed ({clone.Message})");

            LeanCacheProvisioner.VerifyPrivateDirectory(staged);
            RequireWarmMathlib(staged, stateProbe);
            ValidateDonor(selection.Donor, donorLake, pins, runner, stateProbe);
            LeanCacheProvisioner.VerifyPrivateDirectory(lake);
            if (!stamp.AsSpan().SequenceEqual(File.ReadAllBytes(LeanCacheStamp.PathFor(lake))))
                throw new InvalidOperationException("target cache stamp changed during packages staging");
            RequireAbsent(target, stateProbe);
            Directory.Move(staged, target);
            return new LeanCacheProvisionResult(
                "cloned",
                "clonefile",
                null,
                LeanCacheProvisioner.InspectMathlibOleans(lake),
                clonefile);
        }
        catch (Exception exception)
        {
            var exit = new CloneReceiptExit(clonefile);
            exit.TryCleanup(staged, LeanCacheProvisioner.RemovePartial, "packages staging cleanup");
            throw exit.Wrap(exception);
        }
    }

    private static void ValidateDonor(
        string donor,
        string lake,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        ILeanCacheStateProbe stateProbe)
    {
        LeanCacheProvisioner.VerifyPrivateDirectory(lake);
        var packages = Path.Combine(lake, "packages");
        if (!Directory.Exists(packages)
            || File.GetAttributes(packages).HasFlag(FileAttributes.ReparsePoint))
            throw new InvalidOperationException("main checkout packages are not a private directory");
        if (!LeanCacheStamp.Matches(lake, pins, out var stampReason))
            throw new InvalidOperationException(stampReason ?? "main checkout stamp mismatch");
        var project = stateProbe.ProbeOleans(Path.Combine(lake, "build", "lib", "lean"));
        if (!project.IsWarm)
            throw new InvalidOperationException(project.Error ?? "main checkout project layer cold");
        RequireWarmMathlib(packages, stateProbe);
        if (LeanCacheBusyProbe.IsBusy(donor, runner))
            throw new InvalidOperationException("main checkout cache is busy");
    }

    private static void RequireWarmMathlib(string packages, ILeanCacheStateProbe stateProbe)
    {
        var current = packages;
        foreach (var component in new[] { "mathlib", ".lake", "build", "lib", "lean" })
        {
            current = Path.Combine(current, component);
            if (!Directory.Exists(current)
                || File.GetAttributes(current).HasFlag(FileAttributes.ReparsePoint))
                throw new InvalidOperationException("packages mathlib cache is not a private directory");
        }
        var warmth = stateProbe.ProbeOleans(current);
        if (!warmth.IsWarm)
            throw new InvalidOperationException(warmth.Error ?? "packages mathlib layer cold");
    }

    private static void RequireAbsent(string target, ILeanCacheStateProbe stateProbe)
    {
        var content = stateProbe.InspectContentRoot(target);
        if (!content.Clear)
            throw new InvalidOperationException(content.Error ?? "target packages appeared during staging");
    }
}
