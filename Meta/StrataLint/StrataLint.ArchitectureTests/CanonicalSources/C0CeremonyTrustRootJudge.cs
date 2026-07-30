using System.Diagnostics;

namespace StrataLint.ArchitectureTests;

internal static class C0CeremonyTrustRootJudge
{
    internal static void AssertPreimageBlobs(
        string root,
        IEnumerable<C0CeremonyTrustRootTests.C0Record> records,
        string preimageTree)
    {
        foreach (var record in records.Where(static item => item.Kind is
            "c0/controller" or "c0/corpus" or "c0/gate-wiring"))
        {
            Assert.Equal(
                record.Address,
                "git-sha1/" + Git(root, "rev-parse", $"{preimageTree}:{record.Path}"));
        }
    }

    private static string Git(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(
            process.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {process.ExitCode}: {error}");
        return output.TrimEnd('\r', '\n');
    }
}
