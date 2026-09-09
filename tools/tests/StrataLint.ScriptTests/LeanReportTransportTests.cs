using System.Text.Json;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;
using FixtureDirectory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class LeanReportTransportTests
{
    [Theory]
    [InlineData(null, 1800)]
    [InlineData("75", 75)]
    public void BulkTransferDeadlineIsSeparateFromMetadata(string? configured, int expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.SimulateTransferDuration();
        var environment = new[] { "FIXTURE_TRANSFER_SECONDS=31" }
            .Concat(configured is null ? [] : new[] { "STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS=" + configured }).ToArray();
        fixture.Success(fixture.Publish(fixture.Bundle(), environment));
        fixture.Success(fixture.Fetch(environment));
        Assert.Contains($"release upload timeout={expected}", fixture.DeadlineCalls);
        Assert.Contains($"release download timeout={expected}", fixture.DeadlineCalls);
        Assert.Contains("api timeout=30", fixture.DeadlineCalls);
        Assert.All(fixture.DeadlineCalls.Where(value => value.StartsWith("api ", StringComparison.Ordinal)),
            value => Assert.Equal("api timeout=30", value));
    }

    [Theory]
    [InlineData("upload", "0.5", true)]
    [InlineData("upload", "1.25", false)]
    [InlineData("download", "0.5", true)]
    [InlineData("download", "1.25", false)]
    public void BulkTransferDeadlineBoundaryIsAnOptionalFailure(string operation, string duration, bool succeeds)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle();
        if (operation == "download") fixture.Success(fixture.Publish(bundle));
        fixture.SimulateTransferDuration();
        var environment = new[] { "STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS=1",
            "FIXTURE_TRANSFER_OPERATION=" + operation, "FIXTURE_TRANSFER_SECONDS=" + duration };
        var result = operation == "upload" ? fixture.Publish(bundle, environment) : fixture.Fetch(environment);
        Assert.Equal(succeeds, result.ExitCode == 0);
        if (succeeds) return;
        Assert.Contains("timeout_seconds=1", result.Text, StringComparison.Ordinal);
        Assert.Contains("LEAN_REPORT_CACHE status=miss", result.Text, StringComparison.Ordinal);
        Assert.Empty(fixture.CacheEntries);
    }

    [Theory]
    [InlineData("")]
    [InlineData("0")]
    [InlineData("-1")]
    [InlineData("+1")]
    [InlineData("1.5")]
    [InlineData("nan")]
    [InlineData("inf")]
    [InlineData("1\n")]
    [InlineData("86401")]
    [InlineData("999999999999999999999999999999")]
    public void InvalidBulkTransferDeadlinePreventsRemoteIo(string value)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var result = fixture.Publish(fixture.Bundle(), "STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS=" + value);
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS", result.Text, StringComparison.Ordinal);
        Assert.Empty(fixture.ReleaseCalls);
    }

    [Theory]
    [InlineData("FIXTURE_GH_DOWNLOAD_FAIL=existing")]
    [InlineData("FIXTURE_GH_ASSETS_FAIL=1")]
    public void UnavailablePublicationReadPreservesOriginalPairEvenWhenProspectiveUploadFails(string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle();
        fixture.Success(fixture.Publish(bundle));
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var result = fixture.Publish(bundle, failure, "FIXTURE_GH_UPLOAD_FAIL=1");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
        fixture.Success(fixture.Fetch());
    }

    [Theory]
    [InlineData("unpack-directory", "File exists")]
    [InlineData("unpack-write", "Is a directory")]
    [InlineData("verifier", "returned non-zero exit status 69")]
    public void UnavailableLocalVerificationPreservesOriginalPairEvenWhenProspectiveUploadFails(string failure, string diagnostic)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle();
        fixture.Success(fixture.Publish(bundle));
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        LeanReportTransportFixture.Attempt result;
        try { result = fixture.Publish(bundle, "FIXTURE_GH_VERIFY_FAILURE=" + failure, "FIXTURE_GH_UPLOAD_FAIL=1"); }
        finally { fixture.RestoreVerifier(); }
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("fixture download complete phase=existing failure=" + failure, result.Text, StringComparison.Ordinal);
        Assert.Contains(diagnostic, result.Text, StringComparison.Ordinal);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
        fixture.Success(fixture.Fetch());
    }

    [Theory]
    [InlineData("download")]
    [InlineData("unpack-directory")]
    [InlineData("unpack-write")]
    [InlineData("verifier")]
    public void UnavailablePostUploadVerificationDoesNotClaimPublicationSuccess(string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var environment = failure == "download" ? new[] { "FIXTURE_GH_DOWNLOAD_FAIL=published" }
            : new[] { "FIXTURE_GH_VERIFY_FAILURE=" + failure, "FIXTURE_GH_VERIFY_PHASE=published" };
        LeanReportTransportFixture.Attempt result;
        try { result = fixture.Publish(fixture.Bundle(), environment); }
        finally { fixture.RestoreVerifier(); }
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
        Assert.Equal(2, fixture.Assets.Length);
        fixture.Success(fixture.Fetch());
    }

    [Fact]
    public void SameKeyUploadConflictAcceptsVerifiedWinnerWithoutClobber()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var result = fixture.Publish(fixture.Bundle(), "FIXTURE_GH_UPLOAD_RACE=1");
        fixture.Success(result);
        Assert.Contains("mode=existing", result.Text, StringComparison.Ordinal);
        Assert.Equal(1, fixture.UploadCount);
        Assert.DoesNotContain("--clobber", fixture.ReleaseCalls.Single(value => value.StartsWith("release upload ", StringComparison.Ordinal)),
            StringComparison.Ordinal);
        fixture.Success(fixture.Fetch());
    }

    [Theory]
    [InlineData("raw-lean-report.json")]
    [InlineData("candidate-lean-report.json")]
    public void RoundTripNormalizesAllFiveMembersAndImportsUnderPairAddress(string basename)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle(basename);
        fixture.Success(fixture.Publish(bundle));
        fixture.Success(fixture.Fetch());

        Assert.NotEqual(fixture.RepositoryAddress, fixture.PairAddress);
        var restored = fixture.CachedReport;
        foreach (var suffix in LeanReportTransportFixture.Suffixes.Where(value => value != ".sha256"))
            Assert.Equal(FixtureFile.ReadAllBytes(bundle + suffix), FixtureFile.ReadAllBytes(restored + suffix));
        Assert.Equal(LeanReportTransportFixture.Digest(FixtureFile.ReadAllBytes(bundle)) + "  raw-lean-report.json\n",
            FixtureFile.ReadAllText(restored + ".sha256"));
        Assert.False(FixtureDirectory.Exists(Path.Combine(fixture.CacheRoot, fixture.RepositoryAddress)));
        Assert.False(FixtureDirectory.Exists(restored + ".logs"));
        Assert.False(FixtureDirectory.Exists(Path.Combine(fixture.Repository, ".lake")));
        Assert.Equal(2, fixture.Assets.Length);
        Assert.All(fixture.ReleaseCalls, call => Assert.DoesNotContain("lean-cache-v1-", call, StringComparison.Ordinal));
    }

    [Fact]
    public void ExactRemoteHitRunsEnsureBeforeLakeStagingWithoutProducerOrSlot()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        var result = fixture.MakeReport();
        fixture.Success(result);
        Assert.Contains("mode=cached", result.Text, StringComparison.Ordinal);
        Assert.Equal(["absent"], fixture.EnsureCalls);
        Assert.Empty(fixture.ProducerCalls);
        Assert.Empty(fixture.SlotCalls);
        Assert.Contains("mode=exact", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void ExactLocalHitPerformsNoRemoteIoOrProducerSlotButStillEnsures()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.Success(fixture.Fetch());
        var before = fixture.ReleaseCalls;
        fixture.Success(fixture.MakeReport("FIXTURE_GH_FAIL=1"));
        Assert.Equal(before, fixture.ReleaseCalls);
        Assert.Equal(["absent"], fixture.EnsureCalls);
        Assert.Empty(fixture.ProducerCalls);
        Assert.Empty(fixture.SlotCalls);
    }

    [Fact]
    public void EnsureFailureOnExactHitPreservesLiveBundleAndExit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Pair(remote: false));
        var before = fixture.LiveSnapshot();
        var result = fixture.Pair(remote: true, "FIXTURE_ENSURE_EXIT=73");
        Assert.Equal(73, result.ExitCode);
        Assert.Equal(before, fixture.LiveSnapshot());
        Assert.Single(fixture.ProducerCalls);
        Assert.Empty(fixture.ReleaseCalls);
    }

    [Fact]
    public void CompatibleRemoteSeedFeedsAuthoritativeDeltaWithoutClaimingCurrentHit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var oldAddress = fixture.PairAddress;
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.WriteSource("D5/Probe.lean", "-- changed\n");
        var result = fixture.Fetch();
        fixture.Success(result);
        Assert.Contains("mode=seed", result.Text, StringComparison.Ordinal);
        Assert.False(FixtureDirectory.Exists(Path.Combine(fixture.CacheRoot, fixture.PairAddress)));
        Assert.True(FixtureDirectory.Exists(Path.Combine(fixture.CacheRoot, oldAddress)));
        using var plan = fixture.DeltaPlan();
        Assert.Equal("delta", plan.RootElement.GetProperty("status").GetString());
        Assert.Equal(["D5.Probe"], plan.RootElement.GetProperty("recheck").EnumerateArray().Select(value => value.GetString()));
        fixture.Success(fixture.Pair(remote: true));
        Assert.Single(fixture.ProducerCalls);
        Assert.Contains("\"mode\":\"produced\"", FixtureFile.ReadAllText(fixture.Output + ".provenance.json"), StringComparison.Ordinal);
    }

    [Fact]
    public void CompatibleLocalSeedAvoidsRemoteIo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Pair(remote: false));
        fixture.WriteSource("D5/Probe.lean", "-- changed\n");
        fixture.Success(fixture.Pair(remote: true, "FIXTURE_GH_FAIL=1"));
        Assert.Empty(fixture.ReleaseCalls);
        Assert.Equal(2, fixture.ProducerCalls.Length);
    }

    [Theory]
    [InlineData("producer")]
    [InlineData("config")]
    public void IncompatibleProducerOrConfigurationIsNotImported(string input)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.ChangeCompatibility(input);
        Assert.NotEqual(0, fixture.Fetch().ExitCode);
        Assert.Empty(fixture.CacheEntries);
    }

    [Theory]
    [InlineData("archive-digest")]
    [InlineData("materials-digest")]
    [InlineData("materials-zip")]
    [InlineData("missing-materials")]
    [InlineData("missing-provenance")]
    [InlineData("pair-address")]
    [InlineData("repository-address")]
    [InlineData("basename")]
    [InlineData("producer")]
    [InlineData("config")]
    public void DamagedTransportIsAMissBeforeImport(string damage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.DamageAsset(damage);
        var result = fixture.Fetch();
        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(fixture.CacheEntries);
        Assert.Contains("LEAN_REPORT_CACHE status=miss", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("unavailable")]
    [InlineData("missing")]
    [InlineData("cache-write")]
    [InlineData("corrupt")]
    public void AcquisitionFailureFallsBackToRequiredProduction(string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        if (failure == "corrupt")
        {
            fixture.Success(fixture.Publish(fixture.Bundle()));
            fixture.DamageAsset("archive-digest");
        }
        if (failure == "cache-write") fixture.BlockCacheRoot();
        var result = fixture.MakeReport(failure == "unavailable" ? "FIXTURE_GH_FAIL=1" : "FIXTURE_GH_FAIL=0");
        fixture.Success(result);
        Assert.Single(fixture.ProducerCalls);
        Assert.Single(fixture.SlotCalls);
        Assert.Contains("mode=produced", result.Text, StringComparison.Ordinal);
        Assert.Contains("LEAN_REPORT_CACHE status=miss", result.Text, StringComparison.Ordinal);
        if (failure == "cache-write")
            Assert.Contains("reason=cache-write-failed", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void FailedReplacementAfterRemoteMissKeepsEveryLiveBundleByte()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Pair(remote: false));
        var before = fixture.LiveSnapshot();
        fixture.ClearCache();
        var result = fixture.Pair(remote: true, "FIXTURE_GH_FAIL=1", "FIXTURE_PRODUCER_EXIT=69");
        Assert.Equal(69, result.ExitCode);
        Assert.Equal(before, fixture.LiveSnapshot());
    }

    [Theory]
    [InlineData("complete")]
    [InlineData("partial")]
    [InlineData("corrupt")]
    [InlineData("materials-zip")]
    [InlineData("pair-address")]
    public void RepeatedPublicationVerifiesOrRepairsAllAssets(string state)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle();
        fixture.Success(fixture.Publish(bundle));
        if (state == "partial") fixture.RemoveDigestAsset();
        if (state != "complete" && state != "partial")
            fixture.DamageAsset(state == "corrupt" ? "archive-digest" : state);
        var uploads = fixture.UploadCount;
        fixture.Success(fixture.Publish(bundle));
        Assert.Equal(state == "complete" ? uploads : uploads + 1, fixture.UploadCount);
        Assert.Equal(2, fixture.Assets.Length);
        fixture.Success(fixture.Fetch());
    }

    [Theory]
    [InlineData("2026-09-01T00:00:00Z", "2026-09-01T00:00:00Z", "starter")]
    [InlineData("2026-09-01T00:00:00+00:00", "2026-09-01T00:00:00+00:00", "starter")]
    [InlineData("2026-09-01T00:00:00Z", "2026-09-08T00:00:00Z", "unavailable")]
    [InlineData("2026-09-01T00:00:00Z", "2026-09-01T00:00:00", "unavailable")]
    [InlineData("2026-09-01T00:00:00Z", "2026-09-01T00:00:00+01:00", "unavailable")]
    [InlineData("2026-09-01T00:00:00Z", "2026-09-01T00:00:00ZZ", "unavailable")]
    [InlineData("2026-09-01T00:00:00Z", null, "unavailable")]
    [InlineData("2026-09-02T00:00:00Z", "2026-09-01T00:00:00Z", "unavailable")]
    public void StarterPublicationStateParsesUtcTimestampsConservatively(string? created, string? updated, string expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var result = fixture.PublicationState(created, updated);
        fixture.Success(result);
        Assert.Equal(expected, result.Stdout.Trim());
        Assert.Empty(result.Stderr);
        Assert.Empty(fixture.ReleaseCalls);
    }

    [Theory]
    [InlineData("archive")]
    [InlineData("digest")]
    [InlineData("both")]
    public void StarterFailureBecomesRecoverableAfterUploadWindow(string member)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair(member);
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var active = fixture.Publish(bundle, "FIXTURE_NOW=2026-09-08T00:00:00Z");
        Assert.NotEqual(0, active.ExitCode);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Equal(0, fixture.DeleteCount);

        fixture.Success(fixture.Publish(bundle));
        Assert.Equal(uploads + 1, fixture.UploadCount);
        Assert.Equal(2, fixture.DeleteCount);
        Assert.Equal(2, fixture.Assets.Length);
        Assert.All(fixture.AssetStates(), state => Assert.Equal("uploaded", state));
        Assert.DoesNotContain("--clobber", fixture.ReleaseCalls.Last(value => value.StartsWith("release upload ", StringComparison.Ordinal)),
            StringComparison.Ordinal);
        fixture.Success(fixture.Fetch());
        foreach (var suffix in LeanReportTransportFixture.Suffixes.Where(value => value != ".sha256"))
            Assert.Equal(FixtureFile.ReadAllBytes(bundle + suffix), FixtureFile.ReadAllBytes(fixture.CachedReport + suffix));
    }

    [Theory]
    [InlineData("missing-digest")]
    [InlineData("corrupt-archive")]
    [InlineData("unavailable-download")]
    public void StarterRecoveryRequiresCompleteVerifiedPair(string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair();
        var uploads = fixture.UploadCount;
        var result = fixture.Publish(bundle, failure == "unavailable-download"
            ? "FIXTURE_GH_DOWNLOAD_FAIL=published" : "FIXTURE_GH_UPLOADED_DAMAGE=" + failure);
        Assert.Equal(uploads + 1, fixture.UploadCount);
        Assert.Equal(2, fixture.DeleteCount);
        Assert.NotEqual(0, result.ExitCode);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
        Assert.Contains(failure == "corrupt-archive" ? "reason=publication-incomplete" : "reason=publication-unavailable",
            result.Text, StringComparison.Ordinal);
        if (failure == "unavailable-download") fixture.Success(fixture.Fetch());
        else Assert.NotEqual(0, fixture.Fetch().ExitCode);
    }

    [Theory]
    [InlineData("initial-unavailable")]
    [InlineData("confirm-unavailable")]
    [InlineData("confirm-active")]
    [InlineData("confirm-replaced")]
    public void StarterRecoveryMetadataUnavailableOrChangedPreservesAssets(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair();
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var reads = fixture.AssetReadCount;
        var result = fixture.Publish(bundle, "FIXTURE_GH_METADATA_SCENARIO=" + scenario, "FIXTURE_GH_UPLOAD_FAIL=1");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Equal(0, fixture.DeleteCount);
        Assert.Equal(reads + (scenario == "initial-unavailable" ? 1 : 2), fixture.AssetReadCount);
        if (scenario == "confirm-active") Assert.Contains("open", fixture.AssetStates());
    }

    [Theory]
    [InlineData("recent")]
    [InlineData("at-maximum")]
    [InlineData("open")]
    [InlineData("unknown")]
    [InlineData("nonempty")]
    [InlineData("missing-size")]
    [InlineData("missing-time")]
    [InlineData("future")]
    [InlineData("active-companion")]
    public void ActiveOrUncertainStarterIsPreserved(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair();
        var state = scenario is "open" or "unknown" ? scenario : "starter";
        int? size = scenario == "missing-size" ? null : scenario == "nonempty" ? 1 : 0;
        var updated = scenario switch
        {
            "recent" => "2026-09-08T00:00:01Z",
            "at-maximum" => "2026-09-08T00:00:00Z",
            "missing-time" => null,
            "future" => "2026-09-10T00:00:00Z",
            _ => "2026-09-07T00:00:00Z",
        };
        fixture.SetAssetMetadata("", state, size, updated);
        if (scenario == "active-companion") fixture.SetAssetMetadata(".sha256", "open", 0, "2026-09-07T00:00:00Z");
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var result = fixture.Publish(bundle, "STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS=75");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Equal(0, fixture.DeleteCount);
    }

    [Fact]
    public void StarterRecoveryDeletionFailureIsBounded()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair();
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var result = fixture.Publish(bundle, "FIXTURE_GH_DELETE_FAIL=1");
        Assert.Equal(1, fixture.DeleteCount);
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void StarterRecoveryPreservesReplacementCreatedAfterRecheck()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.FailedStarterPair();
        var before = fixture.ReleaseSnapshot();
        var uploads = fixture.UploadCount;
        var result = fixture.Publish(bundle, "FIXTURE_GH_DELETE_RACE=1");
        Assert.Equal(1, fixture.DeleteCount);
        Assert.Equal(uploads, fixture.UploadCount);
        Assert.Equal(before, fixture.ReleaseSnapshot());
        Assert.Contains("open", fixture.AssetStates());
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("reason=publication-unavailable", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("status=published", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void PublicationRejectsStaleInputBeforeRemoteWrite()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var bundle = fixture.Bundle();
        fixture.WriteSource("D5/Probe.lean", "-- changed\n");
        Assert.NotEqual(0, fixture.Publish(bundle).ExitCode);
        Assert.Empty(fixture.ReleaseCalls);
    }

    [Theory]
    [InlineData("complete")]
    [InlineData("partial")]
    [InlineData("corrupt")]
    public void ExactAssetPrecedesCompatibleSeedAndBadExactFallsBack(string state)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        var oldAddress = fixture.PairAddress;
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.WriteSource("D5/Probe.lean", "-- new input\n");
        fixture.Success(fixture.Publish(fixture.Bundle()));
        if (state == "partial") fixture.RemoveDigestAsset();
        if (state == "corrupt") fixture.DamageAsset("archive-digest");
        var result = fixture.Fetch();
        fixture.Success(result);
        Assert.Contains(state == "complete" ? "mode=exact" : "mode=seed", result.Text, StringComparison.Ordinal);
        Assert.Single(fixture.CacheEntries);
        Assert.Contains(state == "complete" ? fixture.PairAddress : oldAddress, fixture.CacheEntries[0], StringComparison.Ordinal);
    }

    [Fact]
    public void TrailingCacheRootSeparatorStillRestoresExactBundle()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        var result = fixture.MakeReport("STRATALINT_REPORT_CACHE_ROOT=" + fixture.CacheRoot + "/");
        fixture.Success(result);
        Assert.Empty(fixture.ProducerCalls);
        Assert.Contains("mode=cached", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void FailedFetchPreservesAlreadyInstalledBundle()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.Publish(fixture.Bundle()));
        fixture.Success(fixture.Fetch());
        var before = fixture.CacheSnapshot();
        fixture.DamageAsset("archive-digest");
        Assert.NotEqual(0, fixture.Fetch().ExitCode);
        Assert.Equal(before, fixture.CacheSnapshot());
    }
}
