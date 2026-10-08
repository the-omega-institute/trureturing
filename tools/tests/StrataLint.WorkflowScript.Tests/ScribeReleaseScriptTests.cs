using StrataLint.Runtime;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class ScribeReleaseScriptTests
{
    private const string Pack = "scribe-resources.zip";
    private const string Carrier = "StrataLint.Scribe.ResourceBundle.dll";
    private static readonly string Digest = new('a', 64);

    [Fact]
    public void PublishUploadsAndVerifiesBothDownloadedAssetsBeforePublication()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();

        var result = fixture.Publish();

        AssertSuccess(result);
        Assert.Equal($"SCRIBE_RELEASE published tag=scribe-resources-{Digest} digest={Digest}", LastLine(result));
        Assert.Equal(new[]
        {
            "build", "verify-release local", "view missing", "create",
            $"upload {Pack}", $"upload {Carrier}",
            $"download {Pack}", $"download {Carrier}", "verify-release downloaded", "edit",
        }, fixture.Events);
        Assert.Equal("false", fixture.State);
        Assert.True(fixture.HasAsset(Pack));
        Assert.True(fixture.HasAsset(Carrier));
    }

    [Fact]
    public void PublishedReleaseMissingCarrierFailsWithNamedAssetAndIsNotDeleted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();
        fixture.Published(includeCarrier: false);

        var result = fixture.Publish();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains($"AssetDownloadFailed: tag=scribe-resources-{Digest} asset={Carrier}", Error(result));
        Assert.Contains($"download {Carrier}", fixture.Events);
        Assert.DoesNotContain("edit", fixture.Events);
        Assert.DoesNotContain("delete", fixture.Events);
        Assert.Equal("false", fixture.State);
    }

    [Fact]
    public void PublishedReleaseWithBothAssetsIsVerifiedAndReused()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();
        fixture.Published();

        var result = fixture.Publish();

        AssertSuccess(result);
        Assert.Equal($"SCRIBE_RELEASE reused tag=scribe-resources-{Digest} digest={Digest}", LastLine(result));
        Assert.Equal(new[]
        {
            "build", "verify-release local", "view false",
            $"download {Pack}", $"download {Carrier}", "verify-release downloaded",
        }, fixture.Events);
    }

    [Theory]
    [InlineData("corrupt-carrier", "ReleaseVerificationFailed")]
    [InlineData("digest", "DigestMismatch")]
    [InlineData("missing-digest", "MissingTotalSha256")]
    public void PublishedReleaseWithInvalidDownloadedAssetsIsRejected(string fault, string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture(fault);
        fixture.Published();

        var result = fixture.Publish();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(failure, Error(result));
        Assert.Contains("verify-release downloaded", fixture.Events);
        Assert.DoesNotContain("edit", fixture.Events);
        Assert.DoesNotContain("delete", fixture.Events);
    }

    [Theory]
    [InlineData("create", "DraftCreateFailed")]
    [InlineData("upload", "UploadFailed")]
    [InlineData("download", "AssetDownloadFailed")]
    [InlineData("verify", "ReleaseVerificationFailed")]
    [InlineData("digest", "DigestMismatch")]
    [InlineData("missing-digest", "MissingTotalSha256")]
    [InlineData("edit", "PublicationFailed")]
    public void FailedNewPublicationDeletesItsDraft(string fault, string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture(fault);

        var result = fixture.Publish();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(failure, Error(result));
        Assert.Equal("missing", fixture.State);
        Assert.Equal("delete", fixture.Events[^1]);
        Assert.False(fixture.HasAsset(Pack));
        Assert.False(fixture.HasAsset(Carrier));
        Assert.DoesNotContain($"SCRIBE_RELEASE published tag=scribe-resources-{Digest}", Output(result));
    }

    [Fact]
    public void FetchOnlyDownloadsAndVerifiesPackWithoutCarrier()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();
        fixture.Published(includeCarrier: false);

        var result = fixture.Fetch();

        AssertSuccess(result);
        Assert.Equal(new[] { "view false", $"download {Pack}", "verify-pack" }, fixture.Events);
        Assert.Contains($"digest={Digest}", LastLine(result));
        Assert.True(File.Exists(Path.Combine(fixture.FetchDirectory, Pack)));
        Assert.False(File.Exists(Path.Combine(fixture.FetchDirectory, Carrier)));
    }

    private static string Output(ProcessOutput result) => Encoding.UTF8.GetString(result.StandardOutput);
    private static string Error(ProcessOutput result) => Encoding.UTF8.GetString(result.StandardError);
    private static string LastLine(ProcessOutput result) => Output(result).TrimEnd().Split('\n')[^1];
    private static void AssertSuccess(ProcessOutput result) => Assert.True(result.ExitCode == 0, Output(result) + Error(result));
}
