using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal sealed class LeanCacheChunkFixture : IDisposable
{
    internal const string Archive = "0123456789abcdefgh";
    internal const string ProducerSha = "0123456789abcdef0123456789abcdef01234567";
    private const string Revision = "4444444444444444444444444444444444444444";
    private readonly TemporaryDirectory temporary = new();
    private readonly string repository;
    private readonly string bin;
    private readonly string script;
    private readonly string owner;
    private readonly string releases;

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    internal LeanCacheChunkFixture(string archive = Archive)
    {
        repository = Path.Combine(temporary.Path, "repo");
        bin = Path.Combine(temporary.Path, "bin");
        releases = Path.Combine(temporary.Path, "releases");
        script = Path.Combine(repository, "tools/scripts/worktree/lean-cache-publish.sh");
        owner = Path.Combine(Path.GetDirectoryName(script)!, "lean_cache_release.py");
        foreach (var directory in new[] { repository, bin, releases, Path.GetDirectoryName(script)!, Path.Combine(repository, ".lake/build") })
            ScriptHarnessScratch.EnsureDirectory(directory);
        foreach (var name in new[] { "lean-cache-publish.sh", "lean_cache_release.py", "lean_cache.py", "cache_material.py" })
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree", name),
                Path.Combine(Path.GetDirectoryName(script)!, name));
        Write(Path.Combine(repository, "lake-manifest.json"), JsonSerializer.Serialize(new
        {
            packages = new[] { new { name = "mathlib", rev = Revision, inputRev = "requested-tag" } },
        }));
        WriteStub("make",
            """printf '%s\n' "$*" >> "$CHUNK_FIXTURE/build-runs"; exit "$FAKE_BUILD_EXIT" """);
        Write(Path.Combine(temporary.Path, "gh.py"), GhProgram);
        WriteStub("gh",
            """exec python3 "$CHUNK_FIXTURE/gh.py" "$@" """);
        var address = Run("address");
        AssertSuccess(address);
        Partition = JsonNode.Parse(address.Text)!["partition"]!.GetValue<string>();
        ArchiveBytes = Pack(archive, Partition);
        FixtureFile.WriteAllBytes(Path.Combine(temporary.Path, "archive"), ArchiveBytes);
        // Replace only the pack dependency in this child interpreter. Fetch uses
        // the real tar reader and installs the verified bytes into the scratch tree.
        Write(Path.Combine(bin, "sitecustomize.py"), """
            import os, pathlib, shutil, tarfile
            original = tarfile.open
            class PackedFixture:
                def __init__(self, path): self.path = path
                def __enter__(self): return self
                def add(self, *args, **kwargs): pass
                def __exit__(self, *args):
                    shutil.copyfile(pathlib.Path(os.environ["CHUNK_FIXTURE"]) / "archive", self.path)
            def open_archive(path, mode="r", **kwargs):
                return PackedFixture(path) if mode == "w:gz" else original(path, mode, **kwargs)
            tarfile.open = open_archive
            """);
    }

    internal string Partition { get; }
    internal byte[] ArchiveBytes { get; }
    internal string Tag => CandidateTag(4242);
    internal string CandidateTag(int run, string? partition = null) => $"lean-cache-v2-{(partition ?? Partition).Replace('/', '-')}-{run}-1";
    internal string? Unpacked => ReadInstalled("build/cache.olean");
    internal string? UnpackedReport => ReadInstalled("report-cache/" + Partition + "/seed.json");
    internal string[] DownloadPatterns => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(temporary.Path, "download-patterns"));
    internal string[] DownloadTags => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(temporary.Path, "download-tags"));
    internal string[][] GhCalls => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(temporary.Path, "gh-calls"))
        .Select(line => JsonSerializer.Deserialize<string[]>(line)!).ToArray();
    internal string[] BuildRuns => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(temporary.Path, "build-runs"));
    internal JsonObject Manifest(string tag) => JsonNode.Parse(ReadAssetText(tag, "manifest.json"))!.AsObject();
    internal JsonObject Metadata(string tag) => JsonNode.Parse(ReadAssetText(tag, "release.json"))!.AsObject();
    internal byte[] ReadAsset(string tag, string name) => FixtureFile.ReadAllBytes(Path.Combine(releases, tag, name));
    private string ReadAssetText(string tag, string name) => FixtureFile.ReadAllText(Path.Combine(releases, tag, name));
    internal string[] Assets(string tag) => Directory.GetFiles(Path.Combine(releases, tag))
        .Select(Path.GetFileName).Where(name => name != "release.json").Order(StringComparer.Ordinal).ToArray()!;
    internal bool HasRelease => Directory.GetDirectories(releases).Length != 0;

    internal void SetChunkBytes(int chunkBytes)
    {
        var text = FixtureFile.ReadAllText(owner);
        var assignment = Assert.Single(text.Split('\n'),
            line => line.StartsWith("CHUNK_BYTES = ", StringComparison.Ordinal));
        Write(owner, text.Replace(assignment, $"CHUNK_BYTES = {chunkBytes}", StringComparison.Ordinal));
    }

    internal Attempt Publish(int? chunkBytes = null, string? chunkEnvironment = null, int run = 4242,
        string? failure = null, int buildExit = 0, string? commit = ProducerSha, string? runId = null)
    {
        if (chunkBytes is not null) SetChunkBytes(chunkBytes.Value);
        return Run("publish", chunkEnvironment: chunkEnvironment, run: runId ?? run.ToString(),
            failure: failure, buildExit: buildExit, commit: commit);
    }

    internal Attempt Fetch(bool allowSeed = false) => Run("fetch", allowSeed);

    internal void ListReleases(params string[] tags)
    {
        for (var i = 0; i < tags.Length; i++)
        {
            var metadata = Metadata(tags[i]);
            metadata["created_at"] = (tags.Length - i).ToString("D8");
            Write(Path.Combine(releases, tags[i], "release.json"), metadata.ToJsonString());
        }
    }

    internal void AddRelease(string tag, bool chunked = true, string? deviation = null, string? partition = null)
    {
        var directory = Path.Combine(releases, tag);
        ScriptHarnessScratch.EnsureDirectory(directory);
        var chunkSize = chunked ? (ArchiveBytes.Length + 2) / 3 : ArchiveBytes.Length;
        var chunks = ArchiveBytes.Chunk(chunkSize).ToArray();
        var parts = new JsonArray();
        for (var i = 0; i < chunks.Length; i++)
        {
            var name = chunks.Length == 1 ? "lean-build.tgz" : $"lean-build.tgz.part-{i:D2}";
            var part = new JsonObject { ["name"] = name, ["sha256"] = Digest(chunks[i]), ["bytes"] = chunks[i].Length };
            if (i == 1 && deviation == "missing-part-digest") part.Remove("sha256");
            if (i == 1 && deviation == "bad-part-size") part["bytes"] = chunks[i].Length + 1;
            parts.Add(part);
            if (i == 1 && deviation == "missing-part") continue;
            var bytes = chunks[i].ToArray();
            if (i == 1 && deviation == "bad-part") bytes[0] ^= 1;
            FixtureFile.WriteAllBytes(Path.Combine(directory, name), bytes);
        }
        var manifest = new JsonObject
        {
            ["schema"] = "lean-release-seed-v3", ["partition"] = partition ?? Partition,
            ["producer_commit_sha"] = ProducerSha, ["workflow_run_id"] = tag.Split('-')[^2],
            ["workflow_run_attempt"] = "1", ["archive_sha256"] = Digest(ArchiveBytes),
            ["archive_bytes"] = ArchiveBytes.Length, ["parts"] = parts,
        };
        if (deviation == "bad-whole") manifest["archive_sha256"] = new string('0', 64);
        if (deviation == "bad-whole-size") manifest["archive_bytes"] = ArchiveBytes.Length + 1;
        if (deviation == "invalid-parts") manifest["parts"] = 0;
        if (deviation == "empty-parts") manifest["parts"] = new JsonArray();
        if (deviation is "missing-parts" or "old-schema") manifest.Remove("parts");
        if (deviation == "old-schema") manifest["schema"] = "lean-release-seed-v2";
        if (deviation == "no-producer") manifest.Remove("producer_commit_sha");
        if (deviation == "no-run-id") manifest.Remove("workflow_run_id");
        if (deviation == "no-attempt") manifest.Remove("workflow_run_attempt");
        if (deviation == "wrong-partition") manifest["partition"] = "f" + Partition[1..];
        Write(Path.Combine(directory, "manifest.json"), manifest.ToJsonString());
        if (deviation == "extra-asset") Write(Path.Combine(directory, "notes.txt"), "undeclared");
        WriteMetadata(tag, deviation);
    }

    internal void AssertSuccess(Attempt result) => Assert.True(result.ExitCode == 0, result.Text);

    private void WriteMetadata(string tag, string? deviation)
    {
        var metadata = new JsonObject
        {
            ["tag_name"] = tag, ["target_commitish"] = deviation == "wrong-target" ? "dev" : ProducerSha,
            ["draft"] = deviation == "draft", ["created_at"] = tag,
            ["download_failure"] = deviation == "download-failure",
            ["assets"] = new JsonArray(Assets(tag).Select(name => (JsonNode)new JsonObject
            {
                ["name"] = name,
                ["digest"] = "sha256:" + (deviation == "bad-github-part-digest" && name.EndsWith("part-01", StringComparison.Ordinal)
                    || deviation == "bad-github-manifest-digest" && name == "manifest.json"
                    ? new string('0', 64) : Digest(ReadAsset(tag, name))),
            }).ToArray()),
        };
        Write(Path.Combine(releases, tag, "release.json"), metadata.ToJsonString());
    }

    private Attempt Run(string verb, bool allowSeed = false, string? chunkEnvironment = null,
        string run = "4242", string? failure = null, int buildExit = 0, string? commit = ProducerSha)
    {
        var arguments = new List<string>
        {
            "-u", "STRATALINT_CACHE_TEST_CHUNK_BYTES",
            $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
            $"HOME={temporary.Path}", $"PYTHONPATH={bin}", $"CHUNK_FIXTURE={temporary.Path}",
            "STRATALINT_CACHE_REPO=fixture/cache", "STRATALINT_ACTIONS_CACHE_SEEDED=",
            $"GITHUB_SHA={commit}", $"GITHUB_RUN_ID={run}", "GITHUB_RUN_ATTEMPT=1",
            "CI=true", "GITHUB_ACTIONS=true", "GITHUB_EVENT_NAME=schedule",
            "GITHUB_REF=refs/heads/dev", "GITHUB_REF_NAME=dev", "LC_ALL=C.UTF-8",
            $"FAKE_FAIL={failure}", $"FAKE_BUILD_EXIT={buildExit}",
        };
        if (chunkEnvironment is not null) arguments.Add($"STRATALINT_CACHE_TEST_CHUNK_BYTES={chunkEnvironment}");
        arguments.AddRange(["/bin/bash", script, verb, "--repository", repository]);
        if (allowSeed) arguments.Add("--allow-seed");
        var result = TestProcessRunner.Run("/usr/bin/env", arguments.ToArray(), repository,
            TestBudgets.WorkflowProcessHangGuard, 256 * 1024);
        return new Attempt(result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    private string? ReadInstalled(string path)
    {
        var fullPath = Path.Combine(repository, ".lake", path);
        return FixtureFile.Exists(fullPath) ? FixtureFile.ReadAllText(fullPath) : null;
    }

    private void WriteStub(string name, string body)
    {
        var path = Path.Combine(bin, name);
        ScriptHarnessScratch.CopyScriptInto(script, path);
        // A BOM before the shebang makes Python's exec skip the fake executable.
        Write(path, "#!/bin/sh\nset -eu\n" + body + "\n");
        Assert.Equal((byte)'#', FixtureFile.ReadAllBytes(path)[0]);
    }

    private static byte[] Pack(string payload, string partition)
    {
        using var output = new MemoryStream();
        using (var gzip = new GZipStream(output, CompressionLevel.SmallestSize, leaveOpen: true))
        using (var tar = new TarWriter(gzip, leaveOpen: true))
        {
            foreach (var (name, value) in new[] { ("build/cache.olean", payload), ("report-cache/" + partition + "/seed.json", "report-seed") })
            {
                using var input = new MemoryStream(Encoding.ASCII.GetBytes(value));
                tar.WriteEntry(new UstarTarEntry(TarEntryType.RegularFile, name)
                {
                    DataStream = input, ModificationTime = DateTimeOffset.UnixEpoch,
                });
            }
        }
        return output.ToArray();
    }

    private static void Write(string path, string text) => ScriptHarnessScratch.WriteScratchText(path, text);
    internal static string Digest(byte[] value) => Convert.ToHexStringLower(SHA256.HashData(value));
    public void Dispose() => temporary.Dispose();
    internal sealed record Attempt(int ExitCode, string Text);

    private const string GhProgram = """
        import fnmatch, hashlib, json, os, pathlib, shutil, sys
        args = sys.argv[1:]
        root = pathlib.Path(os.environ["CHUNK_FIXTURE"])
        with (root / "gh-calls").open("a") as log: log.write(json.dumps(args) + "\n")
        def option(name): return args[args.index(name) + 1]
        def read(directory): return json.loads((directory / "release.json").read_text())
        def save(directory, value): (directory / "release.json").write_text(json.dumps(value))
        def inventory(directory):
            return [{"name": p.name, "digest": "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()}
                    for p in directory.iterdir() if p.name != "release.json"]
        if args[0] == "api":
            assert args[1].startswith("repos/fixture/cache/releases/tags/")
            print(json.dumps(read(root / "releases" / args[1].split("/")[-1])))
            sys.exit(0)
        assert option("--repo") == "fixture/cache"
        if args[:2] == ["release", "list"]:
            print(json.dumps([{"tagName": p.parent.name, "createdAt": read(p.parent)["created_at"],
                              "isDraft": read(p.parent)["draft"]}
                             for p in (root / "releases").glob("*/release.json")]))
            sys.exit(0)
        verb, tag = args[1:3]
        directory = root / "releases" / tag
        if verb == "create":
            directory.mkdir()
            save(directory, {"tag_name": tag, "target_commitish": option("--target"),
                             "created_at": tag, "draft": "--draft" in args})
        elif verb == "upload":
            for value in args[3:args.index("--repo")]:
                source = pathlib.Path(value)
                shutil.copyfile(source, directory / source.name)
                if os.environ["FAKE_FAIL"] == "upload": sys.exit(23)
        elif verb == "edit":
            value = read(directory)
            value["assets"] = inventory(directory)
            value["draft"] = False
            save(directory, value)
        elif verb == "download":
            if read(directory).get("download_failure"): sys.exit(23)
            with (root / "download-tags").open("a") as log: log.write(tag + "\n")
            for i, argument in enumerate(args):
                if argument != "--pattern": continue
                pattern = args[i + 1]
                with (root / "download-patterns").open("a") as log: log.write(pattern + "\n")
                files = [p for p in directory.iterdir() if fnmatch.fnmatchcase(p.name, pattern)]
                if not files: sys.exit(23)
                for source in files: shutil.copyfile(source, pathlib.Path(option("--dir")) / source.name)
        elif verb == "delete": shutil.rmtree(directory)
        else: sys.exit(84)
        """;
}
