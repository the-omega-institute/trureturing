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
        import Lean.PrivateName
        import Lean.Util.CollectAxioms

        open Lean

        def atom (value : String) : String := s!"{value.utf8ByteSize}:{value}"

        partial def encodeName : Name → String
          | .anonymous => "n0"
          | .str parent value => s!"ns({encodeName parent},{atom value})"
          | .num parent value => s!"nn({encodeName parent},{value})"

        partial def encodeLevel : Level → String
          | .zero => "l0"
          | .succ level => s!"ls({encodeLevel level})"
          | .max left right => s!"lm({encodeLevel left},{encodeLevel right})"
          | .imax left right => s!"li({encodeLevel left},{encodeLevel right})"
          | .param name => s!"lp({encodeName name})"
          | .mvar id => s!"lv({encodeName id.name})"

        def encodeBinderInfo : BinderInfo → String
          | .default => "bd"
          | .implicit => "bi"
          | .strictImplicit => "bs"
          | .instImplicit => "bc"

        def encodeLiteral : Literal → String
          | .natVal value => s!"ln({value})"
          | .strVal value => s!"lt({atom value})"

        partial def encodeExpr : Expr → String
          | .bvar index => s!"eb({index})"
          | .fvar id => s!"ef({encodeName id.name})"
          | .mvar id => s!"em({encodeName id.name})"
          | .sort level => s!"es({encodeLevel level})"
          | .const name levels =>
              s!"ec({encodeName name},[{String.intercalate "," (levels.map encodeLevel)}])"
          | .app function argument => s!"ea({encodeExpr function},{encodeExpr argument})"
          | .lam _ type body binderInfo =>
              s!"el({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
          | .forallE _ type body binderInfo =>
              s!"ep({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
          | .letE _ type value body nondependent =>
              s!"ee({if nondependent then "1" else "0"},{encodeExpr type},{encodeExpr value},{encodeExpr body})"
          | .lit literal => s!"ei({encodeLiteral literal})"
          | .mdata _ body => s!"ed({encodeExpr body})"
          | .proj name index body => s!"ej({encodeName name},{index},{encodeExpr body})"

        def encodeStatement (info : ConstantInfo) : String :=
          let parameters := info.levelParams.map encodeName
          let header := s!"statement-v1(uparams=[{String.intercalate "," parameters}],type={encodeExpr info.type}"
          match info with
          | .defnInfo _ | .opaqueInfo _ =>
              match info.value? (allowOpaque := true) with
              | some value => header ++ s!",value={encodeExpr value})"
              | none => header ++ ",value=missing)"
          | _ => header ++ ")"

        def includeInStatement (name : Name) : ConstantInfo -> Bool
          | .thmInfo _ => !(privateToUserName name).isInternalDetail
          | _ => true

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
              ("include_in_statement", toJson (includeInStatement name info)),
              ("name", toJson name.toString),
              ("name_key", toJson (encodeName name)),
              ("kind", toJson (kindOf info)),
              ("type", toJson (encodeStatement info)),
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

        var timing = Environment.GetEnvironmentVariable("STRATALINT_TIMING") == "1";
        var clock = System.Diagnostics.Stopwatch.StartNew();
        void Mark(string phase)
        {
            if (timing)
            {
                Console.Error.WriteLine($"[timing] {phase}: {clock.ElapsedMilliseconds}ms");
                clock.Restart();
            }
        }

        var temporary = Path.Combine(Path.GetTempPath(), "stratalint-lean-" + Guid.NewGuid().ToString("N"));
        var snapshotRoot = Path.Combine(temporary, "repository");
        var packageLink = Path.Combine(snapshotRoot, ".lake", "packages");
        Directory.CreateDirectory(snapshotRoot);
        try
        {
            Materialize(snapshot, snapshotRoot);
            Mark("materialize");
            LinkPinnedPackages(packageLink);
            SeedBuildArtifacts(snapshotRoot);
            Mark("seed");
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

            Mark("lake-build");

            // Content-addressed inspection memo: a module report is keyed by the
            // SHA-256 of its .olean. Lake rebuilds a module's .olean whenever the
            // module or anything upstream changes, so the key self-invalidates and
            // a memo hit is exactly as trustworthy as re-running the inspector.
            // Hits need no lean process at all; only misses are inspected.
            var oleanHashes = new Dictionary<string, string>(StringComparer.Ordinal);
            foreach (var module in modules.Keys)
            {
                var oleanPath = Path.Combine(
                    snapshotRoot, ".lake", "build", "lib", "lean",
                    module.Replace('.', Path.DirectorySeparatorChar) + ".olean");
                if (!File.Exists(oleanPath))
                {
                    throw new InvalidOperationException($"snapshot build left no olean for {module}");
                }

                oleanHashes[module] = Convert.ToHexStringLower(
                    System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(oleanPath)));
            }

            Mark("olean-hash");
            var memo = InspectionMemo.Load(root);
            var pending = modules.Keys
                .Where(module => !memo.TryGet(module, oleanHashes[module], out _))
                .Order(StringComparer.Ordinal)
                .ToArray();

            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
            foreach (var module in modules.Keys)
            {
                if (memo.TryGet(module, oleanHashes[module], out var cached))
                {
                    reports.Add(modules[module], cached);
                }
            }

            if (timing)
            {
                Console.Error.WriteLine($"[timing] memo: hits={modules.Count - pending.Length} misses={pending.Length}");
            }

            if (pending.Length == 0)
            {
                Mark("memo-hit-return");
                return LeanAxiomReport.Create(reports);
            }

            var inspector = Path.Combine(temporary, "Inspector.lean");
            File.WriteAllText(inspector, InspectorSource + "\n", StrictUtf8);
            var arguments = new List<string> { "env", "lean", "--run", inspector };
            arguments.AddRange(pending);
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
                            .ToImmutableArray())
                    {
                        IncludeInStatement = RequiredBoolean(item, "include_in_statement"),
                        NameKey = RequiredString(item, "name_key"),
                    })
                    .OrderBy(static item => item.NameKey, StringComparer.Ordinal)
                    .ToImmutableArray();
                reports.Add(path, new LeanFileReport(imports, declarations));
            }

            var missing = modules.Values.Where(path => !reports.ContainsKey(path)).ToArray();
            if (missing.Length > 0)
            {
                throw new InvalidOperationException(
                    "trusted Lean inspector omitted module reports: " + string.Join(", ", missing));
            }

            foreach (var module in pending)
            {
                memo.Put(module, oleanHashes[module], reports[modules[module]]);
            }

            memo.Save(root);
            Mark("inspect+save");
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

    // Seed the snapshot with the repository's own build artifacts so the snapshot
    // lake build is incremental. Correctness is unaffected: lake re-validates every
    // artifact against its own input-trace hashes and rebuilds on any mismatch. A
    // copy (not a symlink) keeps the judge from writing through into the real tree.
    private void SeedBuildArtifacts(string snapshotRoot)
    {
        var source = Path.Combine(root, ".lake", "build");
        if (!Directory.Exists(source))
        {
            return;
        }

        var destination = Path.Combine(snapshotRoot, ".lake", "build");
        foreach (var directory in Directory.EnumerateDirectories(source, "*", SearchOption.AllDirectories))
        {
            Directory.CreateDirectory(Path.Combine(destination, Path.GetRelativePath(source, directory)));
        }

        Directory.CreateDirectory(destination);
        foreach (var file in Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(destination, Path.GetRelativePath(source, file));
            File.Copy(file, target, overwrite: true);
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

    private static bool RequiredBoolean(JsonElement value, string property) =>
        value.TryGetProperty(property, out var child) && child.ValueKind is JsonValueKind.True or JsonValueKind.False
            ? child.GetBoolean()
            : throw new JsonException($"missing {property}");

    private static string Tail(string value) =>
        value.Length <= 4000 ? value.Trim() : value[^4000..].Trim();
}
