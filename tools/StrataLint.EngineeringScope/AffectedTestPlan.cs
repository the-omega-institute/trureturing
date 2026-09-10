using System.Globalization;
using System.Buffers.Binary;
using Microsoft.CodeAnalysis;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using Microsoft.CodeAnalysis.CSharp;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record ActionInput(string Path, string Identity);
internal sealed record TestAction(string Project, string Assembly, string Scope, string[] Methods, ActionInput[] Inputs,
    string[] Edges, string[] Unknown, string ProjectIdentity, string Producer, string Environment, string Identity)
{
    public TestInputBinding? Binding { get; init; }
    internal bool UsesExplicitValues => Binding is not null && Unknown.Length == 0;
}
internal sealed record TestInputBinding(string Declaration, string Key, string[] Rows, string[] Providers, string Identity);
internal sealed record TestProjectInputs(string Project, ActionInput[] Inputs, string[] Edges, string[] Unknown, string Identity);
[JsonConverter(typeof(TestInputManifestConverter))]
internal sealed record TestInputManifest(int Version, string Candidate, TestProjectInputs[] Projects, TestAction[] Actions);
internal sealed record NativeProject(string Project, string[] Inputs, string[][] Semantics,
    Dictionary<string, string> Properties, string[] Compile, string[] Reference, string[] ProjectReferences, string[] Argument, string[] Generated,
    string GeneratedProvenance);

// Indexes are references into unique tables, not another dependency authority.
// Both current evidence and optional seeds use this one wire representation.
internal sealed class TestInputManifestConverter : JsonConverter<TestInputManifest>
{
    private sealed record Project(string ProjectPath, int[] InputIds, int[] EdgeIds, int[] UnknownIds, string Identity);
    private sealed record Action(string ProjectPath, string Assembly, string Scope, string[] Methods, int[] InputIds,
        int[] EdgeIds, int[] UnknownIds, string ProjectIdentity, string Producer, string Environment, string Identity, TestInputBinding? Binding);
    private sealed record Manifest(int Version, string Candidate, ActionInput[] Inputs, string[] Edges, string[] Unknown,
        Project[] Projects, Action[] Actions);

    public override TestInputManifest Read(ref Utf8JsonReader reader, Type type, JsonSerializerOptions options)
    {
        var wire = JsonSerializer.Deserialize<Manifest>(ref reader, options) ?? throw new InvalidDataException("missing shared manifest");
        if (wire.Version != 4) throw new InvalidDataException("invalid test input manifest version");
        Unique(wire.Inputs); Unique(wire.Edges); Unique(wire.Unknown);
        var plan = new TestInputManifest(wire.Version, wire.Candidate,
            wire.Projects.Select(project => new TestProjectInputs(project.ProjectPath, Resolve(wire.Inputs, project.InputIds),
                Resolve(wire.Edges, project.EdgeIds), Resolve(wire.Unknown, project.UnknownIds), project.Identity)).ToArray(),
            wire.Actions.Select(action => new TestAction(action.ProjectPath, action.Assembly, action.Scope, action.Methods,
                Resolve(wire.Inputs, action.InputIds), Resolve(wire.Edges, action.EdgeIds), Resolve(wire.Unknown, action.UnknownIds),
                action.ProjectIdentity, action.Producer, action.Environment, action.Identity) { Binding = action.Binding }).ToArray());
        AffectedTestPlan.Validate(plan);
        return plan;

        static void Unique<T>(T[] values)
        {
            if (values is null || values.Any(value => value is null) || values.Distinct().Count() != values.Length)
                throw new InvalidDataException("duplicate or missing shared record");
        }
        static T[] Resolve<T>(T[] values, int[] ids)
        {
            if (ids is null || ids.Any(id => id < 0 || id >= values.Length) || ids.Distinct().Count() != ids.Length)
                throw new InvalidDataException("dangling or duplicate shared reference");
            return ids.Select(id => values[id]).ToArray();
        }
    }

    public override void Write(Utf8JsonWriter writer, TestInputManifest plan, JsonSerializerOptions options)
    {
        var inputs = new Dictionary<ActionInput, int>();
        var edges = new Dictionary<string, int>(StringComparer.Ordinal);
        var unknown = new Dictionary<string, int>(StringComparer.Ordinal);
        var projects = plan.Projects.Select(project => new Project(project.Project, Intern(inputs, project.Inputs),
            Intern(edges, project.Edges), Intern(unknown, project.Unknown), project.Identity)).ToArray();
        var actions = plan.Actions.Select(action => new Action(action.Project, action.Assembly, action.Scope, action.Methods,
            Intern(inputs, action.Inputs), Intern(edges, action.Edges), Intern(unknown, action.Unknown),
            action.ProjectIdentity, action.Producer, action.Environment, action.Identity, action.Binding)).ToArray();
        JsonSerializer.Serialize(writer, new Manifest(plan.Version, plan.Candidate, inputs.Keys.ToArray(), edges.Keys.ToArray(),
            unknown.Keys.ToArray(), projects, actions), options);

        static int[] Intern<T>(Dictionary<T, int> table, T[] values) where T : notnull => values.Select(value =>
        {
            if (!table.TryGetValue(value, out var id)) table.Add(value, id = table.Count);
            return id;
        }).ToArray();
    }
}

internal static class AffectedTestPlan
{
    internal const string PathName = CommonExecutionEvidence.RootPath + "/test-inputs.json";
    internal const string NativePath = CommonBuildOutputs.RootPath + "/native-inputs.json";

    internal static TestInputManifest Derive(string root, string candidate, RepositorySnapshot snapshot,
        Dictionary<string, ActionInput> hashes, ExecutionMaterial[] materials)
    {
        var native = CommonExecutionEvidence.Read<NativeProject[]>(root, NativePath);
        var graph = native.ToDictionary(project => project.Project, StringComparer.Ordinal);
        foreach (var node in native)
            foreach (var reference in node.ProjectReferences)
                if (!graph.ContainsKey(Relative(reference))) throw new InvalidDataException("dangling native project reference: " + reference);
        var projects = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot));
        var testSet = projects.ToHashSet(StringComparer.Ordinal);
        var filemap = snapshot.TryGetFile(FileMapLoader.RelativePath, out var mapFile)
            ? FileMapLoader.Parse(mapFile.RawBytes.AsSpan(), FileMapLoader.RelativePath) : null;
        var runtime = native.ToDictionary(project => project.Project, project =>
        {
            var directory = Relative(System.IO.Path.GetDirectoryName(project.Properties["TargetPath"])!) + "/";
            return materials.Where(material => material.Path.StartsWith(directory, StringComparison.Ordinal)).ToArray();
        }, StringComparer.Ordinal);
        var initializers = runtime.Values.SelectMany(items => items)
            .Where(material => material.Path.EndsWith(".dll", StringComparison.Ordinal)).DistinctBy(material => material.Sha256)
            .Where(material => CommonBuildOutputs.HasModuleInitializer(Path.Combine(root, material.Path)))
            .Select(material => material.Sha256).ToHashSet(StringComparer.Ordinal);
        var producer = ProducerIdentity();
        var environment = CommonStages.TestEnvironment(root);
        var cache = new AffectedTestCache(root, TextWriter.Null);
        var actions = new List<TestAction>();
        var projectInputs = new List<TestProjectInputs>();
        var bindingPasses = 0;
        var bindingSeconds = 0.0;
        var callableCount = 0;
        var ownersByPath = new Dictionary<string, ActionInput?>(StringComparer.Ordinal);
        var nativeInputs = native.ToDictionary(node => node.Project, node =>
        {
            var unknown = new SortedSet<string>(StringComparer.Ordinal);
            var inputs = new SortedDictionary<string, ActionInput>(StringComparer.Ordinal);
            foreach (var path in node.Inputs) BindInput(path, inputs, unknown);
            foreach (var pair in node.Semantics) inputs["msbuild:" + pair[0]] = new("msbuild:" + pair[0], pair[1]);
            if (node.Argument.Length == 0) unknown.Add("compiler:missing-command-line:" + node.Project);
            // Metadata capture observes generated files but does not rerun generators.
            if (node.Generated.Length != 0)
                unknown.Add("compiler:generated-provenance-unavailable:" + node.Project);
            inputs["compiler:" + node.Project] = new("compiler:" + node.Project,
                Digest(node.Argument.Select(argument => argument.Replace(root, "@repository", StringComparison.Ordinal))));
            foreach (var source in node.Compile.Concat(node.Generated))
            {
                var path = Relative(source);
                if (!hashes.TryGetValue(path, out var input)) hashes[path] = input = new(path, CommonExecutionEvidence.Hash(source));
                inputs["compile:" + path] = new("compile:" + path, input.Identity);
            }
            return (Inputs: inputs.Values.ToArray(), Unknown: unknown.ToArray());
        }, StringComparer.Ordinal);
        foreach (var project in projects)
        {
            var node = native.Single(item => item.Project == project);
            var commonUnknown = new SortedSet<string>(StringComparer.Ordinal);
            var common = new SortedDictionary<string, ActionInput>(StringComparer.Ordinal);
            // TargetDir inventory owns testhost, adapters, dependencies and copied content.
            foreach (var material in runtime[project])
            {
                common["material:" + material.Path] = new("material:" + material.Path, material.Sha256);
                if (initializers.Contains(material.Sha256)) commonUnknown.Add("runtime:module-initializer:" + material.Path);
            }
            var closure = Closure(node).ToArray();
            foreach (var dependency in closure)
            {
                foreach (var input in nativeInputs[dependency.Project].Inputs) common[input.Path] = input;
                commonUnknown.UnionWith(nativeInputs[dependency.Project].Unknown);
            }
            var projectEdges = closure.SelectMany(item => item.ProjectReferences.Select(reference =>
                item.Project + " -> " + Relative(reference))).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
            var shared = new TestProjectInputs(project, common.Values.ToArray(), projectEdges, commonUnknown.ToArray(), "");
            shared = shared with { Identity = ProjectIdentity(shared) };
            projectInputs.Add(shared);
            var declaration = filemap?.TestInputOwners.SingleOrDefault(owner => owner.Project == project);
            var unknown = new SortedSet<string>(shared.Unknown, StringComparer.Ordinal);
            var inputs = new SortedDictionary<string, ActionInput>(StringComparer.Ordinal);
            string[] methods = [];
            TestInputBinding? binding = null;
            if (declaration is null) unknown.Add("input-owner:unowned-project");
            else if (declaration.Version != 1 || declaration.Contract != TestInputContract.ExplicitValues
                || declaration.Producer != typeof(ScribeExecutionDependencies).FullName + "." + nameof(ScribeExecutionDependencies.Derive)
                || declaration.Verifier != typeof(AffectedTestCache).FullName + "." + nameof(AffectedTestCache.ValidateSource)
                || declaration.Runner != typeof(Program).FullName + "." + nameof(Program.RunTests)
                || declaration.RunnerContract != "StandardXunitInline-v1") unknown.Add("input-owner:unresolved-contract-or-reference");
            else
            {
                var declared = Digest([JsonSerializer.Serialize(declaration)]);
                var key = Digest([shared.Identity, producer, declared]);
                var previous = cache.Seed?.Manifest.Actions.SingleOrDefault(action => action.Project == project);
                if (previous?.Binding is { } prior && prior.Key == key && prior.Declaration == declared)
                {
                    binding = prior;
                    methods = previous.Methods;
                    unknown.UnionWith(previous.Unknown);
                    foreach (var input in previous.Inputs) inputs[input.Path] = input;
                }
                else
                {
                    var started = TimeProvider.System.GetTimestamp();
                    bindingPasses++;
                    try
                    {
                        var assemblies = native.Select(p => p.Properties["AssemblyName"]).ToHashSet(StringComparer.Ordinal);
                        var compilationProjects = closure.Select(item =>
                        {
                            var command = item.Argument.Length == 0 ? null : CSharpCommandLineParser.Default.Parse(item.Argument,
                                Path.GetDirectoryName(Path.Combine(root, item.Project))!, RuntimeEnvironment.GetRuntimeDirectory());
                            var sources = item.Compile.Concat(item.Generated).Distinct(StringComparer.Ordinal).Select(path =>
                                new ScribeTrackedSource(Relative(path), snapshot.TryGetFile(Relative(path), out var file) ? file.Text : File.ReadAllText(path))).ToArray();
                            return new ScribeCompilationProject(item.Project, snapshot.Files.Single(pair => pair.Key.Value == item.Project).Value.Text,
                                item.Properties["AssemblyName"], item.ProjectReferences.Select(Relative).ToArray(), sources, null)
                            {
                                NativeArguments = command,
                                NativeReferences = item.Reference.Where(path => !assemblies.Contains(Path.GetFileNameWithoutExtension(path))).ToArray(),
                            };
                        }).ToArray();
                        using var rows = new StandardXunitRows(Path.GetDirectoryName(node.Properties["TargetPath"])!);
                        var bound = ScribeExecutionDependencies.Derive(new(compilationProjects, new HashSet<string>()), project, rows.Format);
                        methods = bound.Methods;
                        unknown.UnionWith(bound.Unknown);
                        foreach (var path in bound.RuntimeInputs) BindInput(path, inputs, unknown, runtimeInput: true);
                        callableCount += bound.Callables;
                        binding = new(declared, key, bound.Rows, bound.Providers, "");
                        binding = binding with { Identity = BindingIdentity(binding) };
                    }
                    catch (Exception exception) when (AffectedTestCache.CacheFailure(exception) || exception is System.Reflection.TargetInvocationException)
                    { unknown.Add("input-owner:binding-unavailable:" + exception.Message); }
                    finally { bindingSeconds += TimeProvider.System.GetElapsedTime(started).TotalSeconds; }
                }
            }
            var action = new TestAction(project, node.Properties["AssemblyName"], "*", methods, inputs.Values.ToArray(),
                [], unknown.ToArray(), shared.Identity, producer, environment.ForValues(binding is not null && unknown.Count == 0), "") { Binding = binding };
            actions.Add(action with { Identity = Identity(action) });
        }
        foreach (var owner in filemap?.TestInputOwners ?? [])
            if (!testSet.Contains(owner.Project)) throw new InvalidDataException("test input owner does not reference an evaluated required project: " + owner.Project);
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.RootPath + "/binding-cost.json", new {
            passes = bindingPasses, seconds = bindingSeconds, callables = callableCount,
            projects = actions.Count, reusable = actions.Count(action => action.UsesExplicitValues),
            unknown = actions.Count(action => !action.UsesExplicitValues),
            context_queries = environment.Startups, context_seconds = environment.StartupSeconds });
        var plan = new TestInputManifest(4, candidate, projectInputs.ToArray(), actions.ToArray());
        AffectedEnvironmentObservation.Write(root, "seal", plan, candidate, context: environment);
        return plan;

        void BindInput(string path, SortedDictionary<string, ActionInput> inputs, SortedSet<string> unknown, bool runtimeInput = false)
        {
            if (!hashes.TryGetValue(path, out var input))
            {
                var identity = runtimeInput && !System.IO.Path.IsPathFullyQualified(path) ? "unresolved-testhost-relative-path"
                    : File.Exists(System.IO.Path.GetFullPath(path, root)) ? CommonExecutionEvidence.Hash(System.IO.Path.GetFullPath(path, root)) : "absent";
                hashes[path] = input = new(path, identity);
            }
            inputs[path] = input;
            if (!ownersByPath.TryGetValue(path, out var ownership))
            {
                var owners = filemap?.Match(path) ?? [];
                ownersByPath[path] = ownership = owners.Length == 0 ? null : new("ownership:" + path, Digest(owners.Select(owner =>
                    $"{owner.Pattern}|{owner.Kind}|{owner.AdmissionPlane}|{owner.ProducedBy}|{string.Join(',', owner.ConsumedBy)}|{string.Join(',', owner.VerifiedBy)}|{owner.RuntimeDisposition}")));
            }
            if (ownership is null) unknown.Add("filemap:unowned:" + path);
            else inputs[ownership.Path] = ownership;
        }

        string Relative(string path) => System.IO.Path.GetRelativePath(root, System.IO.Path.GetFullPath(path, root)).Replace('\\', '/');
        IEnumerable<NativeProject> Closure(NativeProject node)
        {
            var pending = new Stack<NativeProject>(); pending.Push(node);
            var seen = new HashSet<string>(StringComparer.Ordinal);
            while (pending.TryPop(out var next))
            {
                if (!seen.Add(next.Project)) continue;
                yield return next;
                foreach (var reference in next.ProjectReferences) pending.Push(graph[Relative(reference)]);
            }
        }
    }

    internal static string ProjectIdentity(TestProjectInputs project) => Digest(new[] { "test-project-v1", project.Project }
        .Concat(project.Inputs.Select(input => input.Path + "\0" + input.Identity)).Concat(project.Edges).Concat(project.Unknown));
    internal static string Identity(TestAction action) => Digest(new[] { "test-action-v3", action.Project, action.Assembly, action.Scope,
            action.ProjectIdentity, action.Producer, action.Environment, action.Binding?.Identity ?? "unowned" }.Concat(action.Methods)
        .Concat(action.Inputs.Select(input => input.Path + "\0" + input.Identity)).Concat(action.Edges).Concat(action.Unknown));
    internal static void Validate(TestInputManifest plan)
    {
        if (plan.Version != 4 || plan.Candidate.Length != 64 || !plan.Candidate.All(char.IsAsciiHexDigit)
            || !plan.Projects.Select(project => project.Project).SequenceEqual(plan.Actions.Select(action => action.Project))
            || !plan.Projects.Select(project => project.Project).SequenceEqual(plan.Projects.Select(project => project.Project).Order(StringComparer.Ordinal))
            || plan.Projects.Any(project => project.Identity != ProjectIdentity(project)
                || project.Inputs.Select(input => input.Path).Distinct(StringComparer.Ordinal).Count() != project.Inputs.Length)
            || plan.Projects.Select(project => project.Project).Distinct(StringComparer.Ordinal).Count() != plan.Projects.Length
            || plan.Actions.Any(action => action.Scope != "*" || string.IsNullOrWhiteSpace(action.Assembly)
                || action.Binding is null && action.Unknown.Length == 0
                || !action.Methods.SequenceEqual(action.Methods.Distinct().Order(StringComparer.Ordinal))
                || action.Identity != Identity(action)
                || action.Binding is { } binding && (binding.Declaration.Length != 64 || !binding.Declaration.All(char.IsAsciiHexDigit)
                    || binding.Identity != BindingIdentity(binding)
                    || binding.Key != Digest([action.ProjectIdentity, action.Producer, binding.Declaration])
                    || !binding.Rows.SequenceEqual(binding.Rows.Order(StringComparer.Ordinal))
                    || action.Unknown.Length == 0 && (binding.Rows.Length == 0 || binding.Providers.Length == 0
                        || !action.Methods.SequenceEqual(binding.Rows.Select(row => row.Split('(')[0]).Distinct().Order(StringComparer.Ordinal)))
                    || !binding.Providers.SequenceEqual(binding.Providers.Distinct().Order(StringComparer.Ordinal)))
                || action.Inputs.Select(input => input.Path).Distinct(StringComparer.Ordinal).Count() != action.Inputs.Length
                || !plan.Projects.Any(project => project.Project == action.Project && project.Identity == action.ProjectIdentity
                    && project.Unknown.All(action.Unknown.Contains)))
            || plan.Actions.Select(action => (action.Project, action.Scope)).Distinct().Count() != plan.Actions.Length)
            throw new InvalidDataException("invalid test input manifest");
    }
    internal static string ProducerIdentity() => Digest(new[] { typeof(AffectedTestPlan).Assembly,
        typeof(ScribeExecutionDependencies).Assembly, typeof(Compilation).Assembly, typeof(CSharpCompilation).Assembly,
        typeof(Tomlyn.TomlSerializer).Assembly }.Select(assembly => assembly.ManifestModule.ModuleVersionId.ToString()));
    internal static string BindingIdentity(TestInputBinding binding) => Digest(new[] { "explicit-values-v1", binding.Declaration, binding.Key }
        .Concat(binding.Rows).Concat(binding.Providers));

    internal static TestEnvironmentContext ReadTestEnvironment()
    {
        var environment = new System.Diagnostics.ProcessStartInfo().Environment;
        CommonStages.NormalizeEnvironment(environment);
        return new(EnvironmentKey(environment, CultureInfo.CurrentCulture.Name, CultureInfo.CurrentUICulture.Name, false),
            CultureInfo.CurrentCulture.Name, CultureInfo.CurrentUICulture.Name)
        { WorkingDirectory = Directory.GetCurrentDirectory(), RuntimeMaterial = RuntimeMaterialIdentity() };
    }
    private static string RuntimeMaterialIdentity()
    {
        var paths = new HashSet<string>(StringComparer.Ordinal) { Environment.ProcessPath!,
            Path.ChangeExtension(typeof(Program).Assembly.Location, ".runtimeconfig.json") };
        // Runtime and SDK test launchers are executable inputs too. Resolve the
        // native build's SDK applications from their actual dependency manifests.
        paths.UnionWith(Directory.GetFiles(Path.GetDirectoryName(typeof(object).Assembly.Location)!));
        var sdkRoot = Path.Combine(Path.GetDirectoryName(Environment.ProcessPath!)!, "sdk");
        var inventory = Directory.Exists(sdkRoot) ? Directory.GetDirectories(sdkRoot).Select(Path.GetFileName).Order(StringComparer.Ordinal).ToArray() : [];
        if (File.Exists(NativePath))
            foreach (var version in CommonExecutionEvidence.Read<NativeProject[]>(Directory.GetCurrentDirectory(), NativePath)
                         .Select(project => project.Properties["NETCoreSdkVersion"]).Distinct(StringComparer.Ordinal))
                foreach (var application in new[] { "dotnet", "vstest.console" })
                {
                    var directory = Path.Combine(sdkRoot, version);
                    foreach (var suffix in new[] { ".dll", ".runtimeconfig.json", ".deps.json" }) paths.Add(Path.Combine(directory, application + suffix));
                    using var deps = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, application + ".deps.json")));
                    foreach (var target in deps.RootElement.GetProperty("targets").EnumerateObject())
                    foreach (var library in target.Value.EnumerateObject())
                        if (library.Value.TryGetProperty("runtime", out var assets))
                            foreach (var asset in assets.EnumerateObject())
                            {
                                var path = Path.Combine(directory, asset.Name);
                                paths.Add(File.Exists(path) ? path : Path.Combine(directory, Path.GetFileName(asset.Name)));
                            }
                }
        var observerConfig = Path.ChangeExtension(typeof(Program).Assembly.Location, ".runtimeconfig.json");
        return Digest(inventory.Select(name => "sdk:" + name).Concat(paths.Select(path =>
                (Name: path == observerConfig ? "observer-runtimeconfig" : path, Hash: CommonExecutionEvidence.Hash(path)))
            .OrderBy(material => material.Name, StringComparer.Ordinal).Select(material => material.Name + "=" + material.Hash)));
    }
    internal static string EnvironmentKey(IDictionary<string, string?> environment, string culture, string uiCulture, bool values) =>
        Digest(new[] { RuntimeInformation.RuntimeIdentifier, RuntimeInformation.FrameworkDescription, culture, uiCulture,
            values ? "StandardXunitInline-v1;ExplicitValues;unfiltered" : "xunit-v2/vstest;configuration=Release;cwd=testhost;filter=class" }
            .Concat(environment.Where(entry => values || entry.Key.StartsWith("DOTNET_", StringComparison.Ordinal)
                || entry.Key.StartsWith("COMPlus_", StringComparison.Ordinal) || entry.Key.StartsWith("VSTEST_", StringComparison.Ordinal))
                .OrderBy(entry => entry.Key, StringComparer.Ordinal).Select(entry => entry.Key + "=" + entry.Value)));
    internal static string Digest(IEnumerable<string> values)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        Span<byte> length = stackalloc byte[4];
        foreach (var value in values) { var bytes = Encoding.UTF8.GetBytes(value); BinaryPrimitives.WriteInt32LittleEndian(length, bytes.Length); hash.AppendData(length); hash.AppendData(bytes); }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}

// Use the pinned adapter's formatter for InlineData display identities (including
// escaped/truncated strings). Values are compiler-bound primitives, never user
// objects whose ToString could run code. Multiplicity remains in the row array.
internal sealed class StandardXunitRows : IDisposable
{
    private readonly System.Runtime.Loader.AssemblyLoadContext context = new("finite-xunit-rows", isCollectible: true);
    private readonly System.Reflection.MethodInfo format;
    internal StandardXunitRows(string directory)
    {
        context.Resolving += (_, name) => File.Exists(Path.Combine(directory, name.Name + ".dll"))
            ? context.LoadFromAssemblyPath(Path.Combine(directory, name.Name + ".dll")) : null;
        var assembly = context.LoadFromAssemblyPath(Path.Combine(directory, "xunit.execution.dotnet.dll"));
        format = assembly.GetType("Xunit.Internal.ArgumentFormatter", throwOnError: true)!
            .GetMethod("Format", System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic)!;
    }
    internal string Format(string method, string[] names, object?[] values) => method + "(" + string.Join(", ",
        names.Zip(values).Select(pair => pair.First + ": " + (string)format.Invoke(null, [pair.Second, 1])!)) + ")";
    public void Dispose() => context.Unload();
}
