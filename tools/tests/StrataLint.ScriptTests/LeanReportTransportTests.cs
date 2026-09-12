using System.Text.Json;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;
using FixtureDirectory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class LeanReportTransportTests
{
    [Theory]
    [InlineData("ordinary")]
    [InlineData("zip64")]
    [InlineData("zip64-margin")]
    public void DeltaMergeStreamsCompleteCanonicalMaterials(string boundary) => RunDeltaMergeCase(boundary);

    [Theory]
    [InlineData("missing-member")]
    [InlineData("missing-archive")]
    [InlineData("corrupt-base")]
    [InlineData("corrupt-delta")]
    [InlineData("mismatched-base")]
    [InlineData("mismatched-delta")]
    public void DeltaMergeRejectsMissingOrCorruptMaterialsWithoutPublishing(string damage) => RunDeltaMergeCase(damage);

    private static void RunDeltaMergeCase(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-I", "-B", "-c", DeltaMergeCase,
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), temporary.Path, scenario],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(result.StandardOutput) + System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    private const string DeltaMergeCase = """
        import contextlib, hashlib, io, json, pathlib, runpy, stat, struct, sys, zipfile
        from unittest.mock import patch
        script, root, scenario = sys.argv[1:]
        root = pathlib.Path(root)
        api = runpy.run_path(script)
        statement_address = runpy.run_path(str(pathlib.Path(script).with_name('materials.py')))['statement_address']
        baseline, subset, output, plan = [root / name for name in ('base.json', 'subset.json', 'out.json', 'plan.json')]
        def archive(report): return pathlib.Path(str(report) + '.materials.zip')
        def address(data): return 'sha256:' + hashlib.sha256(data).hexdigest()
        def member(key): return 'sha256/' + key[7:]
        def report(records):
            return ('{"modules": [' + ', '.join(json.dumps(r) for r in records)
                    + '], "schema": "stratalint-raw-lean-report-v2"}\n').encode()
        def record(name, keys, version='current'):
            return dict(module='D5.' + name, source_path='D5/' + name + '.lean',
                        source_sha256=address((name + version).encode()), imports=[],
                        declarations=[dict(type_sha256=k, statement_id=k, include_in_statement=False) for k in keys])
        # More than one allowed read, with a final partial chunk and an empty member.
        large = bytes(range(256)) * 8192 + b'0123456789abcdef\n'
        shared, empty, removed = b'delta material\n' * 1024, b'', b'removed material'
        large_key, shared_key, empty_key, removed_key = map(statement_address, (large, shared, empty, removed))
        stable = record('Stable', [large_key, shared_key])
        changed = record('Changed', [shared_key, empty_key])
        baseline.write_bytes(report([stable, record('Removed', [removed_key]), record('Changed', [removed_key], 'old')]))
        subset.write_bytes(report([changed]))
        plan.write_text(json.dumps(dict(baseline=str(baseline), recheck=['D5.Changed'], removed=['D5.Removed'],
            current={r['module']: dict(path=r['source_path'], source_sha256=r['source_sha256']) for r in (stable, changed)})))
        selected = {large_key: large, shared_key: shared, empty_key: empty}
        base_materials = {removed_key: removed, shared_key: shared, large_key: large}
        delta_materials = {empty_key: empty, shared_key: shared, statement_address(b'unused'): b'unused'}
        def write_archive(path, materials, compression):
            with zipfile.ZipFile(path, 'w') as z:
                for key, data in materials.items():
                    info = zipfile.ZipInfo(member(key), (2001, 2, 3, 4, 5, 6))
                    info.compress_type, info.create_system = compression, 0
                    info.comment, info.extra = b'noncanonical source metadata', b'\xfe\xca\x00\x00'
                    info.external_attr = (stat.S_IFREG | 0o600) << 16
                    # Exercise ZIP64 input even when the output needs no ZIP64 header.
                    with z.open(info, 'w', force_zip64=True) as target: target.write(data)
        if scenario == 'missing-member': del base_materials[large_key]
        if scenario == 'mismatched-base': base_materials[large_key] = b'CRC-valid wrong baseline material'
        if scenario == 'mismatched-delta': delta_materials[shared_key] = b'CRC-valid wrong subset material'
        write_archive(archive(baseline), base_materials, zipfile.ZIP_STORED)
        write_archive(archive(subset), delta_materials,
                      zipfile.ZIP_STORED if scenario == 'corrupt-delta' else zipfile.ZIP_DEFLATED)
        if scenario == 'missing-archive': archive(baseline).unlink()
        if scenario.startswith('corrupt-'):
            damaged, key = (baseline, large_key) if scenario == 'corrupt-base' else (subset, shared_key)
            with zipfile.ZipFile(archive(damaged)) as z: info = z.getinfo(member(key))
            data = bytearray(archive(damaged).read_bytes())
            name_length, extra_length = struct.unpack_from('<HH', data, info.header_offset + 26)
            data[info.header_offset + 30 + name_length + extra_length + info.compress_size - 1] ^= 1
            archive(damaged).write_bytes(data)
        sources_before = {p: p.read_bytes() for p in (baseline, subset, archive(baseline), archive(subset)) if p.exists()}
        output.write_bytes(b'previous report')
        archive(output).write_bytes(b'previous archive')
        sys.argv = [script, 'merge', str(plan), str(subset), str(output)]
        if scenario.startswith(('missing-', 'corrupt-', 'mismatched-')):
            if scenario.startswith('mismatched-'):
                for path in (archive(baseline), archive(subset)):
                    with zipfile.ZipFile(path) as z: assert z.testzip() is None
                diagnostic = io.StringIO()
                with contextlib.redirect_stderr(diagnostic):
                    rc = api['main']()
                assert rc == 1, f'CRC-valid mismatched material accepted: {scenario}, exit={rc}'
                assert 'statement material address mismatch' in diagnostic.getvalue()
            elif scenario.startswith('missing-'):
                diagnostic = io.StringIO()
                with contextlib.redirect_stderr(diagnostic): assert api['main']() == 1
                assert 'statement material is missing for ' + large_key in diagnostic.getvalue()
            else:
                try:
                    api['main']()
                except zipfile.BadZipFile as error:
                    assert 'CRC' in str(error), str(error)
                else: raise AssertionError('corrupt selected material was accepted')
            assert output.read_bytes() == b'previous report'
            assert archive(output).read_bytes() == b'previous archive'
        else:
            # Lower the format threshold to test real ZIP64 writes without a multi-GB fixture.
            limit = {'zip64': len(large) - 1, 'zip64-margin': len(large)}.get(scenario, zipfile.ZIP64_LIMIT)
            expected = io.BytesIO()
            reads = {}
            original_read = zipfile.ZipExtFile.read
            def bounded_read(stream, size=-1):
                assert 0 < size <= 1024 * 1024, f'unbounded material read: {stream.name}, size={size}'
                block = original_read(stream, size)
                reads.setdefault(stream.name, []).append(len(block))
                return block
            with patch.object(zipfile, 'ZIP64_LIMIT', limit):
                # Independent serialization oracle: canonical buffered stdlib writer.
                with zipfile.ZipFile(expected, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
                    for key in sorted(selected):
                        info = zipfile.ZipInfo(member(key), (1980, 1, 1, 0, 0, 0))
                        info.compress_type, info.create_system = zipfile.ZIP_DEFLATED, 3
                        info.external_attr = (stat.S_IFREG | 0o644) << 16
                        z.writestr(info, selected[key])
                with patch.object(zipfile.ZipExtFile, 'read', bounded_read): assert api['main']() == 0
            assert output.read_bytes() == report([changed, stable])
            archive_bytes = archive(output).read_bytes()
            assert archive_bytes == expected.getvalue(), 'canonical ZIP bytes changed'
            names = [member(key) for key in sorted(selected)]
            assert list(reads) == names, reads
            assert sum(n > 0 for n in reads[member(large_key)]) > 1
            with zipfile.ZipFile(archive(output)) as z:
                assert z.namelist() == names and z.testzip() is None
                for key, data in selected.items():
                    info = z.getinfo(member(key))
                    assert z.read(info) == data and sum(reads[info.filename]) == len(data)
                    assert info.file_size == len(data) and info.compress_type == zipfile.ZIP_DEFLATED
                    assert info.date_time == (1980, 1, 1, 0, 0, 0) and info.create_system == 3
                    assert info.external_attr == (stat.S_IFREG | 0o644) << 16
                    extra_length = struct.unpack_from('<H', archive_bytes, info.header_offset + 28)[0]
                    assert extra_length == (20 if len(data) * 1.05 > limit else 0)
        assert not list(root.glob('.lean-delta-materials.*')), 'staging directory leaked'
        assert all(p.read_bytes() == data for p, data in sources_before.items()), 'source bundle changed'
        """;

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
        Assert.Equal(["D5.Probe", "Trureturing"], plan.RootElement.GetProperty("recheck").EnumerateArray().Select(value => value.GetString()));
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
