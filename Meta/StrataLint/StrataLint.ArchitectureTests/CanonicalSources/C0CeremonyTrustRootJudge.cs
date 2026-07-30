using System.Diagnostics;
using System.Text.Json;

namespace StrataLint.ArchitectureTests;

internal static class C0CeremonyTrustRootJudge
{
    internal static void AssertPreimageBlobs(
        string root,
        ReadOnlySpan<byte> certificateBytes,
        IEnumerable<C0CeremonyTrustRootTests.C0Record> records)
    {
        var materializedRecords = records.ToArray();
        var preimageTree = SelectPreimageTree(certificateBytes, materializedRecords);
        foreach (var record in materializedRecords.Where(static item => item.Kind is
            "c0/controller" or "c0/corpus" or "c0/gate-wiring"))
        {
            Assert.Equal(
                record.Address,
                "git-sha1/" + Git(root, "rev-parse", $"{preimageTree}:{record.Path}"));
        }
    }

    private static string SelectPreimageTree(
        ReadOnlySpan<byte> certificateBytes,
        IEnumerable<C0CeremonyTrustRootTests.C0Record> records)
    {
        using var certificate = JsonDocument.Parse(certificateBytes.ToArray());
        var certificateAddress = certificate.RootElement
            .GetProperty("candidate")
            .GetProperty("tree_oid")
            .GetString();
        Assert.NotNull(certificateAddress);
        Assert.StartsWith("git-sha1:", certificateAddress, StringComparison.Ordinal);
        var certificateOid = certificateAddress["git-sha1:".Length..];

        var preimageTree = Assert.Single(
            records,
            static item => item.Kind == "c0/preimage-tree");
        Assert.StartsWith("git-tree/", preimageTree.Address, StringComparison.Ordinal);
        var recordOid = preimageTree.Address["git-tree/".Length..];

        Assert.Equal(certificateOid, recordOid);
        return recordOid;
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
