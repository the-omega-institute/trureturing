using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class QualifiedSourceContextFixture
{
    private static readonly ConcurrentDictionary<(string Before, string After), Lazy<string>> Results = new();
    // All cases use the same current checkout, pins and compiler environment.
    // Only their temporary query sources differ. Keep first-use preparation real,
    // without rebuilding/probing the unchanged checkout for each source pair.
    private static readonly Lazy<bool> CompilerCache = new(() =>
    {
        var ensure = TestProcessRunner.Run("make", ["lean-cache-ensure"], TestRepositoryLayout.FindRoot(),
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(ensure.ExitCode == 0, Encoding.UTF8.GetString(ensure.StandardOutput) + Encoding.UTF8.GetString(ensure.StandardError));
        return true;
    });

    internal static void EnsureCompilerCache() => _ = CompilerCache.Value;
    internal static string Source(string name, string path)
    {
        using var packet = System.Text.Json.JsonDocument.Parse(File.ReadAllBytes(Path.Combine(TestRepositoryLayout.FindRoot(),
            "tools/tests/StrataLint.Tests/Ledger/Fixtures/ContextQualification/sources.json")));
        return packet.RootElement.GetProperty(name + "/" + path).GetString()!;
    }

    internal static byte[] Bytes(RepositorySnapshot current, RepositorySnapshot baseline, string before, string after)
    {
        var raw = Results.GetOrAdd((before, after), key => new Lazy<string>(() => Produce(key.Before, key.After))).Value;
        var data = JsonNode.Parse(raw)!;
        var files = new JsonArray();
        var registrations = new JsonArray();
        foreach (var entry in data["rows"]!.AsArray())
        {
            var side = entry!["side"]!.GetValue<string>();
            var path = RepoPath.CreateKnown(entry["path"]!.GetValue<string>());
            var snapshot = side == "current" ? current : baseline;
            var row = new JsonObject {
                ["side"] = side, ["path"] = path.Value,
                ["sourceSha256"] = LeanSourceContextInput.SourceHash(snapshot.Files[path]),
                ["producerSha256"] = LeanSourceContextInput.ProducerHash(current),
                ["configurationSha256"] = LeanSourceContextInput.ConfigurationHash(current),
                ["graphSha256"] = LeanSourceContextInput.GraphHash(snapshot, path),
                ["interfaces"] = System.Text.Json.JsonSerializer.SerializeToNode(
                    LeanSourceContextInput.InterfaceSources(snapshot, path).Select(f => new {
                        path = f.Path.Value, sourceSha256 = LeanSourceContextInput.SourceHash(f) })),
                ["result"] = entry["result"]!.DeepClone(),
            };
            if (entry["kind"]!.GetValue<string>() == "commands") files.Add(row);
            else
            {
                row["referenceConfigurationSha256"] = LeanSourceContextInput.ConfigurationHash(baseline);
                var origin = data["external"]!.DeepClone();
                var bytes = Encoding.UTF8.GetBytes(origin["source"]!.GetValue<string>());
                origin["sha256"] = Convert.ToHexStringLower(SHA256.HashData(bytes));
                origin["blob"] = Convert.ToHexStringLower(SHA1.HashData(
                    Encoding.UTF8.GetBytes("blob " + bytes.Length + "\0").Concat(bytes).ToArray()));
                origin["package"] = "mathlib";
                origin["url"] = "https://github.com/leanprover-community/mathlib4";
                origin["revision"] = new string('a', 40);
                row["origins"] = new JsonArray(origin);
                registrations.Add(row);
            }
        }
        return Encoding.UTF8.GetBytes(new JsonObject { ["schema"] = LeanSourceContextInput.Schema,
            ["files"] = files, ["registrations"] = registrations }.ToJsonString());
    }

    private static string Produce(string before, string after)
    {
        using var temporary = new TemporaryDirectory();
        EnsureCompilerCache();
        var prepared = JsonNode.Parse(Run("prepare"))!;
        foreach (var source in new[] { "ProbeExternal/Equality.lean", "D5/S0/Carrier/Helper.lean" })
            _ = Run("compile", source);
        Assert.Equal(8, prepared["count"]!.GetValue<int>());
        var rows = new JsonArray();
        for (var index = 0; index < 8; index++)
            rows.Add(JsonNode.Parse(Run("query", index.ToString(System.Globalization.CultureInfo.InvariantCulture))));
        return new JsonObject { ["rows"] = rows, ["external"] = prepared["external"]!.DeepClone() }.ToJsonString();

        string Run(params string[] arguments)
        {
            var result = TestProcessRunner.Run("python3", ["-c", QualifiedSourceContextScripts.ContextProducer, TestRepositoryLayout.FindRoot(),
                before, after, temporary.Path, .. arguments], TestRepositoryLayout.FindRoot(),
                BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }
    }
}
