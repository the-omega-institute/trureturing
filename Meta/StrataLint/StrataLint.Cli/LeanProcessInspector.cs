using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class LeanProcessInspector(string repositoryRoot) : ILeanInspector
{
    private const string Marker = "STRATALINT_TRUSTED_LEAN_JSON\t";

    private const string InspectorSource = """
        import Lean.Environment
        import Lean.CoreM
        import Lean.Util.CollectAxioms

        open Lean

        def kindOf : ConstantInfo → String
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"

        def inspectModule (moduleName : Name) : IO Json := do
          let env ← importModules #[{ module := moduleName }] {} (trustLevel := 0)
          let some moduleIdx := env.getModuleIdx? moduleName
            | throw <| IO.userError s!"module not loaded: {moduleName}"
          let moduleData := env.header.moduleData[moduleIdx]!
          let context : Lean.Core.Context := { fileName := "", fileMap := default, options := {} }
          let state : Lean.Core.State := { env }
          let action : Lean.Core.CoreM (Array Json) := moduleData.constNames.mapM fun name => do
            let env ← getEnv
            let some info := env.setExporting false |>.find? name
              | throwError "declaration missing: {name}"
            let axioms ← Lean.collectAxioms name
            return Json.mkObj [
              ("name", toJson name.toString),
              ("kind", toJson (kindOf info)),
              ("type", toJson (toString (repr info.type))),
              ("axioms", toJson (axioms.map Name.toString))
            ]
          let declarations ← Prod.fst <$> Lean.Core.CoreM.toIO action context state
          return Json.mkObj [
            ("module", toJson moduleName.toString),
            ("imports", toJson (moduleData.imports.map (fun item => item.module.toString))),
            ("declarations", toJson declarations)
          ]

        unsafe def main (args : List String) : IO Unit := do
          initSearchPath (← findSysroot)
          for arg in args do
            let moduleName := arg.toName
            let report ← try
              inspectModule moduleName
            catch exception =>
              pure <| Json.mkObj [("module", toJson moduleName.toString), ("error", toJson exception.toString)]
            IO.println ("STRATALINT_TRUSTED_LEAN_JSON\t" ++ report.compress)
        """;

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly string root = Path.GetFullPath(repositoryRoot);

    public LeanAxiomReport Inspect(RepositorySnapshot snapshot)
    {
        var modules = snapshot.Files.Keys
            .Where(path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToDictionary(
                static path => path.Value == "Trureturing.lean"
                    ? "Trureturing"
                    : path.Value[..^5].Replace('/', '.'),
                static path => path.Value,
                StringComparer.Ordinal);
        if (modules.Count == 0)
        {
            return LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        }

        var temporary = Path.Combine(Path.GetTempPath(), "stratalint-lean-" + Guid.NewGuid().ToString("N"));
        var snapshotRoot = Path.Combine(temporary, "repository");
        var packageLink = Path.Combine(snapshotRoot, ".lake", "packages");
        Directory.CreateDirectory(snapshotRoot);
        try
        {
            Materialize(snapshot, snapshotRoot);
            LinkPinnedPackages(packageLink);
            var build = BoundedProcessRunner.Run(
                "lake",
                new[] { "build" },
                snapshotRoot,
                TimeSpan.FromSeconds(300),
                32 * 1024 * 1024);
            if (build.ExitCode != 0)
            {
                throw new InvalidOperationException(
                    "snapshot lake build failed: " + Tail(StrictUtf8.GetString(build.StandardError)));
            }

            var inspector = Path.Combine(temporary, "Inspector.lean");
            File.WriteAllText(inspector, InspectorSource + "\n", StrictUtf8);
            var arguments = new List<string> { "env", "lean", "--run", inspector };
            arguments.AddRange(modules.Keys.Order(StringComparer.Ordinal));
            var output = BoundedProcessRunner.Run(
                "lake",
                arguments,
                snapshotRoot,
                TimeSpan.FromSeconds(180),
                4 * 1024 * 1024);
            if (output.ExitCode != 0)
            {
                throw new InvalidOperationException(
                    "trusted Lean inspector failed: " + Tail(StrictUtf8.GetString(output.StandardError)));
            }

            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
            foreach (var line in StrictUtf8.GetString(output.StandardOutput).Split('\n'))
            {
                if (!line.StartsWith(Marker, StringComparison.Ordinal)) continue;
                using var document = JsonDocument.Parse(line[Marker.Length..]);
                var rootElement = document.RootElement;
                var module = RequiredString(rootElement, "module");
                if (!modules.TryGetValue(module, out var path) || reports.ContainsKey(path))
                {
                    throw new InvalidOperationException("trusted Lean inspector emitted duplicate or unknown module");
                }

                if (rootElement.TryGetProperty("error", out var error))
                {
                    throw new InvalidOperationException(
                        $"trusted Lean inspector failed for {module}: {error.GetString()}");
                }

                var imports = rootElement.GetProperty("imports")
                    .EnumerateArray()
                    .Select(static item => item.GetString() ?? throw new JsonException("non-string import"))
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToImmutableArray();
                var declarations = rootElement.GetProperty("declarations")
                    .EnumerateArray()
                    .Select(static item => new LeanDeclaration(
                        RequiredString(item, "name"),
                        RequiredString(item, "kind"),
                        RequiredString(item, "type"),
                        item.GetProperty("axioms")
                            .EnumerateArray()
                            .Select(static axiom => axiom.GetString() ?? throw new JsonException("non-string axiom"))
                            .Distinct(StringComparer.Ordinal)
                            .Order(StringComparer.Ordinal)
                            .ToImmutableArray()))
                    .OrderBy(static item => item.Name, StringComparer.Ordinal)
                    .ToImmutableArray();
                reports.Add(path, new LeanFileReport(imports, declarations));
            }

            var missing = modules.Values.Where(path => !reports.ContainsKey(path)).ToArray();
            if (missing.Length > 0)
            {
                throw new InvalidOperationException(
                    "trusted Lean inspector omitted module reports: " + string.Join(", ", missing));
            }

            return LeanAxiomReport.Create(reports);
        }
        catch (Exception exception) when (exception is IOException or TimeoutException or InvalidOperationException or JsonException)
        {
            throw new InvalidOperationException($"Lean environment inspection could not run: {exception.Message}", exception);
        }
        finally
        {
            RemovePackageLink(packageLink);
            Directory.Delete(temporary, recursive: true);
        }
    }

    private static void Materialize(RepositorySnapshot snapshot, string snapshotRoot)
    {
        foreach (var (path, file) in snapshot.Files.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            var destination = Path.Combine(snapshotRoot, path.Value);
            var parent = Path.GetDirectoryName(destination)
                ?? throw new InvalidOperationException($"snapshot path has no parent: {path.Value}");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(destination, file.RawBytes.AsSpan());
        }
    }

    private void LinkPinnedPackages(string packageLink)
    {
        var source = Path.Combine(root, ".lake", "packages");
        if (!Directory.Exists(source))
        {
            return;
        }

        Directory.CreateDirectory(Path.GetDirectoryName(packageLink)
            ?? throw new InvalidOperationException("package link has no parent"));
        Directory.CreateSymbolicLink(packageLink, source);
    }

    private static void RemovePackageLink(string packageLink)
    {
        var info = new DirectoryInfo(packageLink);
        if (info.Exists && info.LinkTarget is not null)
        {
            info.Delete();
        }
    }

    private static string RequiredString(JsonElement value, string property) =>
        value.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.String
            ? child.GetString() ?? throw new JsonException($"null {property}")
            : throw new JsonException($"missing {property}");

    private static string Tail(string value) =>
        value.Length <= 4000 ? value.Trim() : value[^4000..].Trim();
}
