namespace StrataLint.Cli;

internal static class InformationTemplateHistoryCacheSeed
{
    // Optional incremental seed. The existing provisioner owns both donor and
    // target guards and makes a private copy; W never shares writable .lake.
    internal static void Copy(string work, string donor)
    {
        if (Directory.Exists(Path.Combine(work, ".lake"))) return;
        donor = Path.GetFullPath(donor);
        var pins = LeanPinSet.TryReadWorktree(work, out var reason)
            ?? throw new IOException("history cache pins unavailable: " + reason);
        var donorPins = LeanPinSet.TryReadWorktree(donor, out reason);
        if (donorPins is null || !pins.HasSameBytes(donorPins)
            || !LeanCacheStamp.Matches(Path.Combine(donor, ".lake"), pins, out reason))
            throw new IOException("history cache donor differs from candidate pins: " + reason);
        if (!LeanLakeExecutable.TryResolve(out var lake, out reason)) throw new IOException(reason);
        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(work, ".lake"))
            ?? throw new IOException("history cache writer is busy");
        using var selection = new LeanCacheDonorSelection(donor, null);
        LeanCacheProvisioner.Provision(selection, work, pins, lake, new ProductionWorktreeProcessRunner(),
            guard, new ApfsDirectoryCloner());
    }
}
