using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

[System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
internal sealed class LeanReportTransportFixture : IDisposable
{
    internal static readonly string[] Suffixes = ["", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip"];
    private readonly TemporaryDirectory temporary = new();
    private string[]? address;
    private string Bin => Path.Combine(temporary.Path, "bin");
    private string Release => Path.Combine(temporary.Path, "release");
    private string AssetMetadata => Path.Combine(temporary.Path, "asset-metadata.json");
    internal string Repository => Path.Combine(temporary.Path, "repository");
    internal string CacheRoot => Path.Combine(temporary.Path, "cache");
    internal string Output => Path.Combine(Repository, ".lake/build/stratalint/raw-lean-report.json");
    internal string RepositoryAddress => Address[0];
    internal string PairAddress => Digest(Encoding.ASCII.GetBytes("schema=stratalint-lean-report-input-v1\n"
        + $"producer_sha256={Address[1]}\nrepository_inspector_sha256={Address[1]}\n"
        + $"lean_sources_sha256={Address[2]}\nlean_config_sha256={Address[3]}\n"));
    internal string CachedReport => Path.Combine(CacheRoot, PairAddress, "raw-lean-report.json");
    internal string[] ReleaseCalls => Calls("gh.log");
    internal string[] DeadlineCalls => Calls("deadline.log");
    internal string[] EnsureCalls => Calls("ensure.log");
    internal string[] ProducerCalls => Calls("producer.log");
    internal string[] SlotCalls => Calls("slot.log");
    internal int UploadCount => ReleaseCalls.Count(value => value.StartsWith("release upload ", StringComparison.Ordinal));
    internal int DeleteCount => ReleaseCalls.Count(value => value.StartsWith("api --method DELETE ", StringComparison.Ordinal));
    internal int AssetReadCount => ReleaseCalls.Count(value => value.Contains("/releases/42/assets?", StringComparison.Ordinal));
    internal string[] Assets => Directory.Exists(Release)
        ? Directory.EnumerateFiles(Release, "*", SearchOption.TopDirectoryOnly).Order(StringComparer.Ordinal).ToArray() : [];
    internal string[] CacheEntries => Directory.Exists(CacheRoot)
        ? Directory.EnumerateFiles(CacheRoot, "raw-lean-report.json", SearchOption.AllDirectories).ToArray() : [];
    private string[] Address
    {
        get
        {
            if (address is not null) return address;
            var result = Run(["/bin/bash", Path.Combine(Repository, "tools/scripts/report/lean-report-input.sh"),
                "address", "--repository", Repository]);
            Success(result);
            address = result.Stdout.Trim().Split(' ');
            Assert.Equal(4, address.Length);
            return address;
        }
    }

    internal LeanReportTransportFixture()
    {
        Directory.CreateDirectory(Bin);
        foreach (var path in new[] { "Makefile", "tools/scripts/report/lean-report.sh", "tools/scripts/lean-report-pair.sh",
                     "tools/scripts/report/lean-report-input.sh", "tools/scripts/report/lean-report-ci-baseline.sh",
                     "tools/scripts/report/lean-report-cache.sh", "tools/scripts/report/lean-report-cache.py",
                     "tools/scripts/worktree/lean-cache-input.sh", "tools/lean-inspector/delta.py" })
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(Repository, path));
        WriteSource("lean-toolchain", "leanprover/lean4:v4.31.0\n");
        WriteSource("lakefile.toml", "name = \"fixture\"\n");
        WriteSource("lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
        WriteSource("Trureturing.lean", "import D5.Probe\n");
        WriteSource("D5/Probe.lean", "-- initial\n");
        WriteSource("tools/lean-inspector/Inspector.lean", "-- synthetic inspector\n");
        WriteSource("tools/scripts/worktree/lean-cache-publish.sh", "#!/usr/bin/env bash\n");
        WriteSource("tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        WriteSource(string.Join('/', ".github", "workflows", "ci.yml"),
            "jobs:\n  lean-inspect:\n    steps: []\n  baseline-admission:\n    steps: []\n");
        foreach (var project in new[] { "StrataLint.Cli", "StrataLint.Engine", "Trureturing.Truth" })
        {
            WriteSource($"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            WriteSource($"tools/{project}/Probe.cs", "// compile input\n");
        }
        Stub("tools/lean-inspector/inspect.sh", ProducerStub);
        Stub("tools/scripts/report/report-supervisor.sh", "printf 'slot\\n' >> \"$REPORT_FIXTURE/slot.log\"\n"
            + "while [[ \"$1\" != -- ]]; do shift; done\nshift\nexec \"$@\"");
        Stub("tools/scripts/worktree/lean-cache-ensure.sh", "state=absent\n[[ ! -e \"$REPORT_REPOSITORY/.lake\" ]] || state=present\n"
            + "printf '%s\\n' \"$state\" >> \"$REPORT_FIXTURE/ensure.log\"\nexit \"${FIXTURE_ENSURE_EXIT:-0}\"");
        Executable(Path.Combine(Bin, "dotnet"), "[[ \"$1\" == msbuild ]]\n"
            + "printf '{\"Items\":{\"Compile\":[{\"FullPath\":\"%s/Probe.cs\"}]}}\\n' \"$(dirname \"$2\")\"");
        Executable(Path.Combine(Bin, "gh"), GithubStub);
        File.WriteAllText(Path.Combine(Bin, "sitecustomize.py"), PublicationClockStub);
    }

    internal void WriteSource(string relative, string text)
    {
        var path = Path.Combine(Repository, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, text);
        address = null;
    }

    internal string Bundle(string basename = "candidate-lean-report.json")
    {
        var bundle = Path.Combine(temporary.Path, "bundle", basename);
        Directory.CreateDirectory(Path.GetDirectoryName(bundle)!);
        var records = new[] { ("D5.Probe", "D5/Probe.lean"), ("Trureturing", "Trureturing.lean") }.Select(item => new
        {
            module = item.Item1, source_path = item.Item2,
            source_sha256 = "sha256:" + Digest(File.ReadAllBytes(Path.Combine(Repository, item.Item2))),
            imports = item.Item1 == "Trureturing" ? new[] { "D5.Probe" } : [], declarations = Array.Empty<object>(),
        });
        File.WriteAllText(bundle, "{\"modules\": [" + string.Join(", ", records.Select(value => JsonSerializer.Serialize(value)))
            + "], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        var digest = Digest(File.ReadAllBytes(bundle));
        File.WriteAllText(bundle + ".sha256", $"{digest}  {basename}\n");
        File.WriteAllText(bundle + ".input.attestation", "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={RepositoryAddress}\nproducer_sha256={Address[1]}\nreport_sha256={digest}\n");
        File.WriteAllText(bundle + ".provenance.json", JsonSerializer.Serialize(new
        {
            schema = "stratalint-lean-report-provenance-v1", side = "candidate", mode = "produced", source_side = "candidate",
            input_address = "sha256:" + PairAddress, producer_sha256 = Address[1], repository_inspector_sha256 = Address[1],
            lean_sources_sha256 = Address[2], lean_config_sha256 = Address[3], report_sha256 = digest,
        }) + "\n");
        File.WriteAllBytes(bundle + ".materials.zip", Zip(new Dictionary<string, byte[]> { ["sha256/fixture"] = [1, 2, 3] }));
        Directory.CreateDirectory(bundle + ".logs");
        File.WriteAllText(bundle + ".logs/producer.log", "diagnostic only\n");
        return bundle;
    }

    internal Attempt Publish(string bundle, params string[] environment) => Run(["make", "lean-report-cache-to-github", $"LEAN_REPORT={bundle}"], environment);
    internal Attempt Fetch(params string[] environment) => Run(["make", "lean-report-cache-from-github"], environment);
    internal Attempt MakeReport(params string[] environment) => Run(["make", "lean-report"], environment);
    internal Attempt PublicationState(string? created, string? updated)
    {
        const string archive = "report-fixture.zip";
        var inventory = Path.Combine(temporary.Path, "publication-state.json");
        File.WriteAllText(inventory, JsonSerializer.Serialize(new[] { new[] { new
        {
            id = 123456, name = archive, state = "starter", size = 0, created_at = created, updated_at = updated,
        } } }));
        // Keep the injected clock parseable on Python 3.9 independently of the
        // production parser: the metadata itself carries the UTC Z regression.
        return Run(["python3", Path.Combine(Repository, "tools/scripts/report/lean-report-cache.py"),
            "publication-state", inventory, archive, "86400"], "FIXTURE_NOW=2026-09-09T00:00:00+00:00");
    }
    internal Attempt Pair(bool remote, params string[] environment) => Run(["/bin/bash",
        Path.Combine(Repository, "tools/scripts/lean-report-pair.sh"), "--producer", Path.Combine(Repository, "tools/lean-inspector/inspect.sh"),
        "--lake-bin", "/bin/echo", "--candidate-root", Repository, "--candidate-output", Output],
        environment.Concat(new[] { "STRATALINT_REPORT_CACHE_REMOTE=" + (remote ? "1" : "0") }).ToArray());

    internal JsonDocument DeltaPlan()
    {
        var modules = Path.Combine(temporary.Path, "modules.tsv");
        var plan = Path.Combine(temporary.Path, "plan.json");
        File.WriteAllText(modules, "D5.Probe\tD5/Probe.lean\n");
        Success(Run(["python3", Path.Combine(Repository, "tools/lean-inspector/delta.py"), "plan", Repository, CacheRoot,
            PairAddress, Address[1], Address[1], Address[3], modules, plan]));
        return JsonDocument.Parse(File.ReadAllBytes(plan));
    }

    internal void ChangeCompatibility(string input)
    {
        var relative = input == "producer" ? "tools/lean-inspector/inspect.sh" : "lakefile.toml";
        WriteSource(relative, File.ReadAllText(Path.Combine(Repository, relative)) + "# changed\n");
    }

    internal void BlockCacheRoot() => File.WriteAllText(CacheRoot, "unavailable\n");
    internal void ClearCache() { if (Directory.Exists(CacheRoot)) Directory.Delete(CacheRoot, true); }
    internal string[] LiveSnapshot() => Suffixes.Select(suffix => Digest(File.ReadAllBytes(Output + suffix)))
        .Append(Digest(File.ReadAllBytes(Output + ".logs/producer.log"))).ToArray();
    internal string[] CacheSnapshot() => Suffixes.Select(suffix => Digest(File.ReadAllBytes(CachedReport + suffix))).ToArray();
    internal string[] ReleaseSnapshot() => Assets.Select(path => Path.GetFileName(path) + "=" + Digest(File.ReadAllBytes(path))).ToArray();
    internal void SimulateTransferDuration() => File.WriteAllText(Path.Combine(Bin, "sitecustomize.py"), PublicationClockStub + "\n" + TransferClockStub);
    internal void RestoreVerifier() => File.Delete(Path.Combine(Bin, "bash"));
    internal string FailedStarterPair(string member = "both")
    {
        var bundle = Bundle();
        var result = Publish(bundle, "FIXTURE_GH_STARTER_FAILURE=" + member, "FIXTURE_NOW=2026-09-07T00:00:00Z");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("HTTP 502", result.Text, StringComparison.Ordinal);
        return bundle;
    }
    internal void SetAssetMetadata(string suffix, string state, int? size, string? updated)
    {
        var metadata = JsonNode.Parse(File.ReadAllBytes(AssetMetadata))!;
        var asset = metadata["assets"]![Path.GetFileName(CurrentArchive) + suffix]!;
        asset["state"] = state;
        if (size is null) asset.AsObject().Remove("size"); else asset["size"] = size.Value;
        if (updated is null) asset.AsObject().Remove("updated_at"); else asset["updated_at"] = updated;
        File.WriteAllText(AssetMetadata, metadata.ToJsonString());
    }
    internal string[] AssetStates()
    {
        var metadata = JsonNode.Parse(File.ReadAllBytes(AssetMetadata))!;
        return Assets.Select(path => metadata["assets"]![Path.GetFileName(path)]!["state"]!.GetValue<string>()).ToArray();
    }
    internal void RemoveDigestAsset() => File.Delete(CurrentArchive + ".sha256");
    private string CurrentArchive => Assets.Single(value => value.EndsWith("-" + RepositoryAddress + ".zip", StringComparison.Ordinal));

    internal void DamageAsset(string damage)
    {
        var archive = CurrentArchive;
        if (damage == "archive-digest") { File.WriteAllText(archive, "broken\n"); return; }
        using var input = new MemoryStream(File.ReadAllBytes(archive));
        using var zip = new ZipArchive(input, ZipArchiveMode.Read);
        var members = zip.Entries.ToDictionary(entry => entry.FullName, entry =>
        {
            using var stream = entry.Open();
            using var bytes = new MemoryStream();
            stream.CopyTo(bytes);
            return bytes.ToArray();
        }, StringComparer.Ordinal);
        const string raw = "raw-lean-report.json";
        if (damage.StartsWith("missing-", StringComparison.Ordinal))
            members.Remove(raw + (damage == "missing-materials" ? ".materials.zip" : ".provenance.json"));
        else if (damage == "materials-zip") members[raw + ".materials.zip"] = Encoding.ASCII.GetBytes("not zip");
        else if (damage == "materials-digest") members[raw + ".materials.zip"] = Zip(new Dictionary<string, byte[]> { ["other"] = [4] });
        else if (damage == "repository-address")
            members[raw + ".input.attestation"] = Encoding.ASCII.GetBytes(Encoding.ASCII.GetString(members[raw + ".input.attestation"])
                .Replace(RepositoryAddress, new string('a', 64), StringComparison.Ordinal));
        else if (damage == "basename")
            members[raw + ".sha256"] = Encoding.ASCII.GetBytes(Encoding.ASCII.GetString(members[raw + ".sha256"])
                .Replace(raw, "candidate-lean-report.json", StringComparison.Ordinal));
        else
        {
            var provenance = JsonNode.Parse(members[raw + ".provenance.json"])!;
            provenance[damage == "pair-address" ? "input_address" : damage + "_sha256"] =
                (damage == "pair-address" ? "sha256:" : "") + new string('a', 64);
            if (damage == "config")
            {
                provenance.AsObject().Remove("config_sha256");
                provenance["lean_config_sha256"] = new string('a', 64);
            }
            members[raw + ".provenance.json"] = Encoding.ASCII.GetBytes(provenance.ToJsonString());
        }
        File.WriteAllBytes(archive, Zip(members));
        if (damage != "materials-digest")
            File.WriteAllText(archive + ".sha256", Digest(File.ReadAllBytes(archive)) + "  " + Path.GetFileName(archive) + "\n");
    }

    private static byte[] Zip(Dictionary<string, byte[]> members)
    {
        using var bytes = new MemoryStream();
        using (var zip = new ZipArchive(bytes, ZipArchiveMode.Create, leaveOpen: true))
            foreach (var (name, content) in members)
            {
                var entry = zip.CreateEntry(name);
                entry.LastWriteTime = new DateTimeOffset(2000, 1, 1, 0, 0, 0, TimeSpan.Zero);
                using var output = entry.Open();
                output.Write(content);
            }
        return bytes.ToArray();
    }

    internal void Success(Attempt result) => Assert.True(result.ExitCode == 0, result.Text);
    internal static string Digest(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
    private string[] Calls(string name) => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(temporary.Path, name));
    private void Stub(string relative, string body) => Executable(Path.Combine(Repository, relative), body);
    private static void Executable(string path, string body)
    {
        ScriptHarnessScratch.WriteExecutableStub(path, body);
        // execvp on macOS can skip a BOM-prefixed script and try the next PATH
        // executable. Preserve the fixture mode but write a real shebang at byte 0.
        File.WriteAllText(path, "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n", new UTF8Encoding(false));
    }
    private Attempt Run(string[] command, params string[] environment)
    {
        File.Delete(Path.Combine(temporary.Path, "asset-reads"));
        var arguments = new[] { "-u", "STRATALINT_REPORT_CACHE_REMOTE", "-u", "STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS",
            $"PYTHONPATH={Bin}", $"PATH={Bin}:{Environment.GetEnvironmentVariable("PATH")}", $"REPORT_FIXTURE={temporary.Path}",
            $"REPORT_REPOSITORY={Repository}", $"STRATALINT_REPORT_CACHE_ROOT={CacheRoot}", "STRATALINT_REPORT_CACHE_REPO=fixture/cache",
            "GH_TOKEN=synthetic-fixture-token", "GITHUB_TOKEN=synthetic-fixture-token",
            "LAKE_BIN=/bin/echo", "CI=true", "GITHUB_ACTIONS=true", "GITHUB_EVENT_NAME=push",
            "GITHUB_REF=refs/heads/dev", "GITHUB_SHA=0123456789abcdef0123456789abcdef01234567", "GITHUB_RUN_ID=42" }
            .Concat(environment).Concat(command).ToArray();
        try
        {
            var result = TestProcessRunner.Run("env", arguments, Repository, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            return new Attempt(result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput), Encoding.UTF8.GetString(result.StandardError));
        }
        catch (SkipException exception)
        {
            throw new SkipException(exception.Message + "; command=" + string.Join(' ', command)
                + "; observed-gh-calls=" + string.Join(" | ", ReleaseCalls));
        }
    }
    public void Dispose() => temporary.Dispose();
    internal sealed record Attempt(int ExitCode, string Stdout, string Stderr) { internal string Text => Stdout + Stderr; }

    // Explicit UTC input for publication abandonment; no elapsed real time.
    private const string PublicationClockStub = """
        import datetime, os, time
        time.time = lambda: datetime.datetime.fromisoformat(os.environ.get('FIXTURE_NOW', '2026-09-09T00:00:00Z')).timestamp()
        """;

    // Inject elapsed IO time at subprocess.run's deadline boundary. The command
    // still executes the real fake-gh transport on success; no wall clock or
    // machine performance decides these tests, and production has no clock hook.
    private const string TransferClockStub = """
        import os, pathlib, subprocess
        original_run = subprocess.run
        def run(args, *positional, **keywords):
            if pathlib.Path(args[0]).name == 'gh':
                operation = ' '.join(args[1:3]) if args[1] == 'release' else args[1]
                deadline = keywords.get('timeout')
                with (pathlib.Path(os.environ['REPORT_FIXTURE']) / 'deadline.log').open('a') as log:
                    log.write(f'{operation} timeout={deadline}\n')
                selected = os.environ.get('FIXTURE_TRANSFER_OPERATION')
                if operation in ('release upload', 'release download') and (not selected or operation == 'release ' + selected):
                    duration = float(os.environ['FIXTURE_TRANSFER_SECONDS'])
                    if deadline is not None and duration >= deadline:
                        raise subprocess.TimeoutExpired(args, deadline)
            return original_run(args, *positional, **keywords)
        subprocess.run = run
        """;

    private const string ProducerStub = """
        printf 'produce\n' >> "$REPORT_FIXTURE/producer.log"
        [[ "${FIXTURE_PRODUCER_EXIT:-0}" == 0 ]] || exit "$FIXTURE_PRODUCER_EXIT"
        while [[ $# -gt 0 ]]; do
          case "$1" in --repository) repository="$2"; shift 2 ;; --output) output="$2"; shift 2 ;; *) exit 2 ;; esac
        done
        python3 - "$repository" "$output" <<'PY'
        import hashlib, json, pathlib, sys, zipfile
        root, out = map(pathlib.Path, sys.argv[1:])
        modules = []
        for name, path in [('D5.Probe', 'D5/Probe.lean'), ('Trureturing', 'Trureturing.lean')]:
            modules.append(dict(module=name, source_path=path, source_sha256='sha256:'+hashlib.sha256((root/path).read_bytes()).hexdigest(), imports=['D5.Probe'] if name == 'Trureturing' else [], declarations=[]))
        out.write_text('{"modules": ['+', '.join(json.dumps(m) for m in modules)+'], "schema": "stratalint-raw-lean-report-v2"}\n')
        pathlib.Path(str(out)+'.sha256').write_text(hashlib.sha256(out.read_bytes()).hexdigest()+'  '+out.name+'\n')
        with zipfile.ZipFile(str(out)+'.materials.zip', 'w') as z:
            z.writestr(zipfile.ZipInfo('sha256/fixture'), b'material')
        logs = pathlib.Path(str(out)+'.logs')
        logs.mkdir()
        (logs/'producer.log').write_text('diagnostic\n')
        PY
        """;

    private const string GithubStub = """
        printf '%s\n' "$*" >> "$REPORT_FIXTURE/gh.log"
        [[ "${FIXTURE_GH_FAIL:-0}" == 0 ]] || exit 69
        python3 - "$@" <<'PY'
        import fnmatch, hashlib, json, os, pathlib, shutil, sys, zipfile
        args = sys.argv[1:]
        root = pathlib.Path(os.environ['REPORT_FIXTURE']) / 'release'
        metadata_path = root.parent / 'asset-metadata.json'
        metadata = json.loads(metadata_path.read_text()) if metadata_path.exists() else dict(next_id=1, assets={})
        def value(flag): return args[args.index(flag)+1]
        def save(): metadata_path.write_text(json.dumps(metadata))
        def record(target, state='uploaded'):
            now = os.environ.get('FIXTURE_NOW', '2026-09-09T00:00:00Z')
            metadata['assets'][target.name] = dict(id=metadata['next_id'], name=target.name, state=state,
                size=target.stat().st_size, created_at=now, updated_at=now)
            metadata['next_id'] += 1
            save()
        def asset(p):
            return dict(metadata['assets'][p.name], digest='sha256:'+hashlib.sha256(p.read_bytes()).hexdigest())
        if args[0] == 'api':
            endpoint = next(a for a in args[1:] if a.startswith('repos/'))
            if not root.is_dir(): raise SystemExit(1)
            if '--method' in args:
                assert value('--method') == 'DELETE' and '/releases/assets/' in endpoint
                identity = int(endpoint.rsplit('/', 1)[1])
                target = next((root / name for name, item in metadata['assets'].items() if item['id'] == identity), None)
                if os.environ.get('FIXTURE_GH_DELETE_FAIL') == '1': raise SystemExit(69)
                if target is not None and os.environ.get('FIXTURE_GH_DELETE_RACE') == '1':
                    record(target, 'open')
                    raise SystemExit(1)
                if target is None or not target.exists(): raise SystemExit(1)
                target.unlink()
                del metadata['assets'][target.name]
                save()
            elif '/tags/' in endpoint:
                assert endpoint.endswith('/lean-report-cache-v1')
                print(42 if '--jq' in args else json.dumps(dict(id=42)))
            else:
                assert '/releases/42/assets' in endpoint
                counter = root.parent / 'asset-reads'
                count = int(counter.read_text()) + 1 if counter.exists() else 1
                counter.write_text(str(count))
                if os.environ.get('FIXTURE_GH_ASSETS_FAIL') == '1': raise SystemExit(69)
                scenario = os.environ.get('FIXTURE_GH_METADATA_SCENARIO')
                if scenario == 'initial-unavailable' or (scenario == 'confirm-unavailable' and count == 2): raise SystemExit(69)
                if count == 2 and scenario in ('confirm-active', 'confirm-replaced'):
                    target = next(p for p in root.iterdir() if p.suffix == '.zip')
                    if scenario == 'confirm-active': metadata['assets'][target.name]['state'] = 'open'
                    else: metadata['assets'][target.name]['id'] += 1000
                    save()
                assets = [asset(p) for p in root.iterdir()]
                print(json.dumps([assets] if '--slurp' in args else assets))
        elif args[:2] == ['release', 'create']:
            assert args[2] == 'lean-report-cache-v1' and '--latest=false' in args
            root.mkdir()
        elif args[:2] == ['release', 'upload']:
            assert args[2] == 'lean-report-cache-v1'
            sources = [pathlib.Path(a) for a in args[3:] if a.startswith('/') and pathlib.Path(a).is_file()]
            if os.environ.get('FIXTURE_GH_UPLOAD_RACE') == '1':
                archive = next(p for p in sources if p.suffix == '.zip')
                target = root / archive.name
                shutil.copyfile(archive, target)
                with zipfile.ZipFile(target, 'a') as z: z.comment = b'independent successful publisher'
                (root / (target.name + '.sha256')).write_text(hashlib.sha256(target.read_bytes()).hexdigest() + '  ' + target.name + '\n')
                record(target)
                record(root / (target.name + '.sha256'))
                raise SystemExit(1)
            starter = os.environ.get('FIXTURE_GH_STARTER_FAILURE')
            for source in sources:
                target = root / source.name
                if target.exists():
                    if '--clobber' not in args: raise SystemExit(1)
                    target.unlink()
                if os.environ.get('FIXTURE_GH_UPLOAD_FAIL') == '1': raise SystemExit(69)
                if starter == 'both' or starter == ('archive' if source.suffix == '.zip' else 'digest'):
                    target.write_bytes(b'')
                    record(target, 'starter')
                else:
                    shutil.copyfile(source, target)
                    record(target)
            if starter:
                print('HTTP 502: Bad Gateway; empty starter asset left by upstream', file=sys.stderr)
                raise SystemExit(1)
            damage = os.environ.get('FIXTURE_GH_UPLOADED_DAMAGE')
            if damage:
                target = next(root / p.name for p in sources if p.suffix == '.zip')
                if damage == 'missing-digest': pathlib.Path(str(target)+'.sha256').unlink()
                elif damage == 'corrupt-archive': target.write_bytes(b'broken')
        elif args[:2] == ['release', 'download']:
            assert args[2] == 'lean-report-cache-v1'
            destination = pathlib.Path(value('--dir'))
            if os.environ.get('FIXTURE_GH_DOWNLOAD_FAIL') in ('any', destination.name): raise SystemExit(69)
            for pattern in [args[i+1] for i,a in enumerate(args) if a == '--pattern']:
                matches = [p for p in root.iterdir() if fnmatch.fnmatchcase(p.name, pattern) and asset(p)['state'] == 'uploaded']
                if not matches: raise SystemExit(1)
                for p in matches: shutil.copyfile(p, destination/p.name)
            failure = os.environ.get('FIXTURE_GH_VERIFY_FAILURE')
            if failure and destination.name == os.environ.get('FIXTURE_GH_VERIFY_PHASE', 'existing'):
                print(f'fixture download complete phase={destination.name} failure={failure}', file=sys.stderr)
                # Fail actual local operations only after both assets arrived.
                if failure == 'unpack-directory':
                    (destination/'bundle').write_text('blocks extraction directory\n')
                elif failure == 'unpack-write':
                    (destination/'bundle'/'raw-lean-report.json').mkdir(parents=True)
                elif failure == 'verifier':
                    bash = pathlib.Path(os.environ['REPORT_FIXTURE']) / 'bin' / 'bash'
                    bash.write_text('#!/bin/sh\nif [ "${2-}" = coordinates ]; then exit 69; fi\nexec /bin/bash "$@"\n')
                    bash.chmod(0o755)
                else: raise SystemExit('unsupported verification failure: '+failure)
        else: raise SystemExit('unsupported fake gh: '+repr(args))
        PY
        """;
}
