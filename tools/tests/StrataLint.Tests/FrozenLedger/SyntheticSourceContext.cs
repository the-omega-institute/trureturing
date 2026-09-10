using System.Collections.Immutable;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Explicit synthetic parser facts for existing unit fixtures (including term fragments).
// This factory is not a production parser. Real compiler/importer composition is tested
// separately by SourceContext producer fixtures and the qualified writer cases.
internal static class SyntheticSourceContext
{
    private static readonly HashSet<string> Starts = new(StringComparer.Ordinal) {
        "import", "module", "prelude", "public", "meta", "namespace", "section", "end", "mutual", "open",
        "variable", "variables", "include", "omit", "universe", "set_option", "attribute", "export",
        "theorem", "lemma", "def", "abbrev", "opaque", "axiom", "inductive", "structure", "class",
        "instance", "constant", "example", "macro", "macro_rules", "syntax", "notation", "local", "scoped",
        "private", "protected", "noncomputable", "partial", "unsafe", "@",
    };

    internal static Func<int, bool> Equality(string source, bool available = true)
    {
        var facts = Facts(source, available);
        return offset => facts.Sites.GetValueOrDefault(offset);
    }

    internal static LeanSourceContextInput ForSnapshots(RepositorySnapshot current, RepositorySnapshot baseline)
    {
        var rows = new JsonArray();
        foreach (var (snapshot, side) in new[] { (current, "current"), (baseline, "protected") })
        foreach (var file in snapshot.Files.Values.Where(file => LeanClosureValidator.IsManagedLean(file.Path.Value)))
        {
            bool available;
            int header;
            try
            {
                available = HasRegistration(snapshot, file, new HashSet<RepoPath>());
                header = LeanSourceHeader.Read(file.Text).End;
            }
            catch (LeanSourceExtractionException) { continue; } // malformed fixtures have no parser facts
            var facts = Facts(file.Text, available);
            var commands = new JsonArray();
            var tokens = facts.Tokens;
            var starts = Enumerable.Range(0, tokens.Length).Where(i => Starts.Contains(tokens[i].Text)
                && (i == 0 || tokens[i - 1].Line < tokens[i].Line
                    || tokens[i - 1].Text == "in")).ToArray();
            for (var i = 0; i < starts.Length; i++)
            {
                var token = tokens[starts[i]];
                if (token.ByteOffset < header) continue;
                var stop = i + 1 < starts.Length ? tokens[starts[i + 1]].ByteOffset : file.RawBytes.Length;
                if (stop <= token.ByteOffset) continue;
                var children = new JsonArray();
                foreach (var (offset, equality) in facts.Sites.Where(site => site.Key >= token.ByteOffset && site.Key < stop))
                    children.Add(new JsonObject { ["start"] = offset, ["end"] = offset + 2,
                        ["kind"] = "fixture.equalitySite", ["namespace"] = facts.Namespaces.GetValueOrDefault(token.ByteOffset, ""),
                        ["equality"] = equality, ["children"] = new JsonArray() });
                commands.Add(new JsonObject { ["start"] = token.ByteOffset, ["end"] = stop,
                    ["kind"] = "fixture.command", ["namespace"] = facts.Namespaces.GetValueOrDefault(token.ByteOffset, ""),
                    ["equality"] = false, ["children"] = children });
            }
            rows.Add(new JsonObject { ["side"] = side, ["path"] = file.Path.Value,
                ["sourceSha256"] = LeanSourceContextInput.SourceHash(file),
                ["producerSha256"] = LeanSourceContextInput.ProducerHash(current),
                ["configurationSha256"] = LeanSourceContextInput.ConfigurationHash(current),
                ["graphSha256"] = LeanSourceContextInput.GraphHash(snapshot, file.Path),
                ["interfaces"] = System.Text.Json.JsonSerializer.SerializeToNode(
                    LeanSourceContextInput.InterfaceSources(snapshot, file.Path).Select(source => new {
                        path = source.Path.Value, sourceSha256 = LeanSourceContextInput.SourceHash(source) })),
                ["origins"] = new JsonArray(),
                ["result"] = new JsonObject { ["headerEnd"] = header, ["initialEquality"] = false,
                    ["isModule"] = LeanSourceHeader.Read(file.Text).IsModule,
                    ["imports"] = System.Text.Json.JsonSerializer.SerializeToNode(LeanSourceHeader.Read(file.Text).Imports.Select(i =>
                        new { module = i.Module, importAll = i.ImportAll, isExported = i.IsExported, isMeta = i.IsMeta })),
                    ["error"] = facts.Error is null ? null : new JsonObject { ["line"] = facts.Error.Line ?? 1,
                        ["message"] = facts.Error.Message }, ["commands"] = commands } });
        }
        var registrations = new JsonArray();
        foreach (var row in rows)
        {
            var registration = row!.DeepClone();
            registration["referenceConfigurationSha256"] = LeanSourceContextInput.ConfigurationHash(baseline);
            var snapshot = registration["side"]!.GetValue<string>() == "current" ? current : baseline;
            var path = RepoPath.CreateKnown(registration["path"]!.GetValue<string>());
            registration["origins"] = Origins(snapshot, baseline, path);
            registrations.Add(registration);
        }
        return LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(new JsonObject {
            ["schema"] = LeanSourceContextInput.Schema, ["files"] = rows,
            ["registrations"] = registrations }.ToJsonString()), current, baseline);
    }

    private static JsonArray Origins(RepositorySnapshot snapshot, RepositorySnapshot reference, RepoPath path)
    {
        var origins = new JsonArray();
        using var manifest = System.Text.Json.JsonDocument.Parse(reference.TryGetFile("lake-manifest.json", out var file) ? file.Text : "{}");
        var modules = LeanSourceContextInput.InterfaceSources(snapshot, path).Prepend(snapshot.Files[path])
            .SelectMany(f => LeanSourceHeader.Read(f.Text).Imports).Select(i => i.Module).Distinct(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            if (snapshot.TryGetFile(module.Replace('.', '/') + ".lean", out _)) continue;
            var core = module.Split('.')[0] is "Init" or "Lean" or "Std";
            var package = !core && manifest.RootElement.TryGetProperty("packages", out var packages)
                ? packages.EnumerateArray().FirstOrDefault() : default;
            if (!core && package.ValueKind != System.Text.Json.JsonValueKind.Object) continue;
            const string source = "prelude\n";
            var data = Encoding.UTF8.GetBytes(source);
            origins.Add(new JsonObject {
                ["module"] = module, ["source"] = source,
                ["sha256"] = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(data)),
                ["blob"] = Convert.ToHexStringLower(System.Security.Cryptography.SHA1.HashData(Encoding.UTF8.GetBytes("blob " + data.Length + "\0" + source))),
                ["package"] = core ? "lean4" : package.GetProperty("name").GetString(),
                ["revision"] = core ? new string('a', 40) : package.GetProperty("rev").GetString(),
                ["pin"] = reference.TryGetFile("lean-toolchain", out var pin) ? pin.Text.Trim() : "",
                ["url"] = core ? "https://github.com/leanprover/lean4" : package.GetProperty("url").GetString(),
                ["path"] = (core ? "src/" : "") + module.Replace('.', '/') + ".lean",
            });
        }
        return origins;
    }

    private static bool HasRegistration(RepositorySnapshot snapshot, RepositoryFile file, HashSet<RepoPath> seen)
    {
        if (!seen.Add(file.Path)) return false;
        foreach (var import in LeanSourceHeader.Read(file.Text).Imports)
        {
            if (import.Module.StartsWith("Mathlib.ModelTheory.", StringComparison.Ordinal)) return true;
            if (snapshot.TryGetFile(import.Module.Replace('.', '/') + ".lean", out var dependency)
                && HasRegistration(snapshot, dependency, seen)) return true;
        }
        return false;
    }

    private static (ImmutableArray<LeanSourceToken> Tokens, Dictionary<int, bool> Sites,
        Dictionary<int, string> Namespaces, LeanSourceExtractionException? Error) Facts(string source, bool available)
    {
        if (source.StartsWith("import Init\n", StringComparison.Ordinal)) available = false;
        var scope = new FixtureScope(available);
        var sites = new Dictionary<int, bool>();
        var namespaces = new Dictionary<int, string>();
        var tokens = ImmutableArray.CreateBuilder<LeanSourceToken>();
        LeanSourceExtractionException? error = null;
        try
        {
            LeanSourceTokenizer.TokenizeIncludingInterpolationTerms(source, offset => {
                var prefix = Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(source).AsSpan(0, offset));
                var line = 1 + prefix.Count(c => c == '\n');
                scope.BeforeToken(line, prefix.Length - prefix.LastIndexOf('\n') - 1);
                return sites[offset] = scope.IsActive;
            }, token => {
                scope.BeforeToken(token.Line, token.Column);
                namespaces[token.ByteOffset] = scope.Namespace;
                tokens.Add(token);
                scope.Observe(token);
            });
        }
        catch (LeanSourceExtractionException exception) { error = exception; }
        return (tokens.ToImmutable(), sites, namespaces, error);
    }

    private sealed class FixtureScope(bool available)
    {
        private readonly List<LeanSourceToken> header = [];
        private readonly Stack<(string Namespace, bool Active)> scopes = new();
        private string currentNamespace = string.Empty;
        private int previousLine;
        private bool commandStart;
        private bool localBodyPending;
        private bool? localRestore;

        private bool active;
        internal bool IsActive { get => available && active; private set => active = value; }
        internal string Namespace => currentNamespace;

        internal void BeforeToken(int line, int column)
        {
            _ = column;
            commandStart = line > previousLine;
            if (!commandStart)
            {
                return;
            }

            FinishHeader(local: false);
            if (localRestore is { } previous && !localBodyPending && column == 0)
            {
                IsActive = previous;
                localRestore = null;
            }
        }

        internal void Observe(LeanSourceToken token)
        {
            previousLine = token.Line;
            if (localBodyPending)
            {
                commandStart = true;
                localBodyPending = false;
            }

            if (commandStart)
            {
                commandStart = false;
                if (token.Text is "open" or "namespace" or "section" or "noncomputable" or "end")
                {
                    header.Add(token);
                }
            }
            else if (header.Count > 0)
            {
                if (header[0].Text == "open" && token.Text == "in")
                {
                    localRestore ??= IsActive;
                    FinishHeader(local: true);
                    localBodyPending = true;
                }
                else
                {
                    header.Add(token);
                }
            }
        }

        private void FinishHeader(bool local)
        {
            if (header.Count == 0)
            {
                return;
            }

            var command = header[0].Text;
            if (command == "open")
            {
                // Elab.Open activates simple/scoped/hiding opens, but not selective
                // or renaming opens. Parser.withOpenDeclFnCore additionally leaves
                // hiding opens inactive while parsing the body of `open ... in`.
                if (!header.Any(token => token.Text is "(" or "renaming")
                    && !(local && header.Any(token => token.Text == "hiding")))
                {
                    IsActive |= header.Skip(1).TakeWhile(token => token.Text != "hiding")
                        .Any(token => token.IsIdentifier && token.Identifier is "FirstOrder" or "_root_.FirstOrder");
                }
            }
            else if (command == "end")
            {
                var count = header.Count > 1 ? header[1].IdentifierParts.Length : 1;
                for (var part = 0; part < count && scopes.TryPop(out var previous); part++)
                {
                    (currentNamespace, IsActive) = previous;
                }
            }
            else
            {
                var section = header.FindIndex(token => token.Text == "section");
                if (command == "namespace" || section >= 0)
                {
                    var nameIndex = command == "namespace" ? 1 : section + 1;
                    var parts = nameIndex < header.Count ? header[nameIndex].IdentifierParts : [];
                    foreach (var part in parts.IsDefaultOrEmpty ? ImmutableArray.Create(string.Empty) : parts)
                    {
                        scopes.Push((currentNamespace, IsActive));
                        if (command == "namespace")
                        {
                            currentNamespace = currentNamespace.Length == 0 ? part : currentNamespace + "." + part;
                            IsActive |= currentNamespace == "FirstOrder";
                        }
                    }
                }
            }

            header.Clear();
        }
    }

}
