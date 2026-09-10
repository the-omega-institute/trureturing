using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Current source compiler")]
public sealed class LeanSourceHeaderProducerTests(SourceCompilerFixture compiler)
{
    [Fact]
    public void BoundedHeaderReaderMatchesCurrentCompilerDescriptorsAndOffsets()
    {
        var sources = new[] {
            "import Init\nexample : ')' =')' := by decide\n",
            "module\nprelude\npublic import Init\nmeta import Lean\nimport all Std\nexample : True := by trivial\n",
            "module\npublic meta import Init\nmeta import all Lean\n",
            "-- α\n/- outer /- nested -/ end -/\nimport Foo.«bar.baz»\n#check Missing\n",
            "prelude\nimport «Init»\n/-! body documentation -/\ntheorem x : True := by trivial\n",
            "import Init\n/-- declaration documentation -/\nexample : True := by trivial\n",
            "-- only trivia\n",
        };
        using var temporary = new TemporaryDirectory();
        var request = Path.Combine(temporary.Path, "headers.json");
        File.WriteAllText(request, JsonSerializer.Serialize(sources.Select(source =>
            new { mode = "header", source, path = "D5/Header.lean", options = Array.Empty<object>() })));
        var root = compiler.Root;
        var query = TestProcessRunner.Run("lake", ["env", "lean", "--run",
            Path.Combine(root, "tools/lean-inspector/SourceContext.lean"), request, temporary.Path], root,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(query.ExitCode == 0, Encoding.UTF8.GetString(query.StandardOutput) + Encoding.UTF8.GetString(query.StandardError));
        using var json = JsonDocument.Parse(query.StandardOutput);
        var rows = json.RootElement.EnumerateArray().ToArray();
        Assert.Equal(sources.Length, rows.Length);
        for (var i = 0; i < sources.Length; i++)
        {
            Assert.Equal(JsonValueKind.Null, rows[i].GetProperty("error").ValueKind);
            var bounded = LeanSourceHeader.Read(sources[i]);
            Assert.Equal(bounded.IsModule, rows[i].GetProperty("isModule").GetBoolean());
            Assert.Equal(bounded.End, rows[i].GetProperty("headerEnd").GetInt32());
            Assert.Equal(bounded.Imports, rows[i].GetProperty("imports").EnumerateArray().Select(row =>
                new LeanSourceImport(row.GetProperty("module").GetString()!, row.GetProperty("importAll").GetBoolean(),
                    row.GetProperty("isExported").GetBoolean(), row.GetProperty("isMeta").GetBoolean())));
        }
    }
}
