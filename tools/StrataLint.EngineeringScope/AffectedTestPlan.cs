using System.Globalization;
using System.Buffers.Binary;
using Microsoft.CodeAnalysis;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis.CSharp;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.EngineeringScope;

internal sealed record ActionInput(string Path, string Identity);
internal sealed record TestAction(string Project, string Assembly, string Scope, string[] Methods, ActionInput[] Inputs,
    string[] Edges, string[] Unknown, string ProjectIdentity, string Producer, string Environment, string Identity);
internal sealed record TestProjectInputs(string Project, ActionInput[] Inputs, string[] Edges, string[] Unknown, string Identity);
internal sealed record TestInputManifest(int Version, string Candidate, TestProjectInputs[] Projects, TestAction[] Actions);
internal sealed record NativeProject(string Project, string[] Inputs, string[][] Semantics,
    Dictionary<string, string> Properties, string[] Compile, string[] Reference, string[] ProjectReferences, string[] Argument, string[] Generated);

internal static class AffectedTestPlan
{
    internal const string PathName = CommonExecutionEvidence.RootPath + "/test-inputs.json";
    internal const string NativePath = CommonBuildOutputs.RootPath + "/native-inputs.json";

    internal static TestInputManifest Derive(string root, string candidate, RepositorySnapshot snapshot,
        Dictionary<string, ActionInput> hashes, ExecutionMaterial[] materials)
    {
        var native = CommonExecutionEvidence.Read<NativeProject[]>(root, NativePath);
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
        var sourceTexts = new Dictionary<string, string>(StringComparer.Ordinal);
        var assemblies = native.Select(project => project.Properties["AssemblyName"]).ToHashSet(StringComparer.Ordinal);
        var compilationProjects = native.Select(project =>
        {
            var command = project.Argument.Length == 0 ? null : CSharpCommandLineParser.Default.Parse(project.Argument,
                Path.GetDirectoryName(System.IO.Path.Combine(root, project.Project))!, RuntimeEnvironment.GetRuntimeDirectory());
            var sources = project.Compile.Concat(project.Generated).Distinct(StringComparer.Ordinal).Select(path =>
            {
                var relative = Relative(path);
                if (!sourceTexts.TryGetValue(relative, out var text))
                    sourceTexts[relative] = text = snapshot.TryGetFile(relative, out var file) ? file.Text : File.ReadAllText(path);
                return new ScribeTrackedSource(relative, text);
            }).ToArray();
            return new ScribeCompilationProject(project.Project, snapshot.Files.Single(pair => pair.Key.Value == project.Project).Value.Text,
                project.Properties["AssemblyName"], project.ProjectReferences.Select(Relative).ToArray(), sources,
                snapshot.TryGetFile(System.IO.Path.GetDirectoryName(project.Project) + "/packages.lock.json", out var packageLock) ? packageLock.Text : null)
            {
                NativeArguments = command,
                NativeReferences = project.Reference.Where(path => !assemblies.Contains(System.IO.Path.GetFileNameWithoutExtension(path))).ToArray(),
            };
        }).ToArray();
        var compilationUnknown = new Dictionary<string, string[]>(StringComparer.Ordinal);
        BoundTestScope[] scopes;
        string? failure = null;
        try { scopes = ScribeExecutionDependencies.Derive(new(compilationProjects, new HashSet<string>())
        {
            ObserveCompilation = (project, compilation) => compilationUnknown[project] = ScribeExecutionDependencies.CompilationUnknown(compilation),
        }, testSet); }
        catch (Exception exception) when (exception is InvalidOperationException or IOException or ArgumentException)
        { scopes = []; failure = "bound-dependencies-unavailable:" + exception.Message; }
        var producer = ProducerIdentity();
        var environment = EnvironmentIdentity();
        var actions = new List<TestAction>();
        var projectInputs = new List<TestProjectInputs>();
        foreach (var project in projects)
        {
            var node = native.Single(item => item.Project == project);
            var projectScopes = scopes.Where(scope => scope.Project == project).ToArray();
            if (projectScopes.Length == 0) projectScopes = [new(project, "*", [], [], [], [failure ?? "adapter:no-bound-test-identities"])];
            var commonUnknown = new SortedSet<string>(StringComparer.Ordinal);
            if (projectScopes.Any(item => item.Unknown.Contains("adapter:custom-or-configured-test-attribute", StringComparer.Ordinal)))
                commonUnknown.Add("adapter:project-discovery-or-skip-configuration");
            var common = new SortedDictionary<string, ActionInput>(StringComparer.Ordinal);
            foreach (var path in node.Inputs) BindInput(path, common, commonUnknown);
            foreach (var pair in node.Semantics) common["msbuild:" + pair[0]] = new("msbuild:" + pair[0], pair[1]);
            // TargetDir inventory owns testhost, adapters, dependencies and copied content.
            foreach (var material in runtime[project])
            {
                common["material:" + material.Path] = new("material:" + material.Path, material.Sha256);
                if (initializers.Contains(material.Sha256)) commonUnknown.Add("runtime:module-initializer:" + material.Path);
            }
            var closure = Closure(node, native).ToArray();
            foreach (var dependency in closure)
            {
                if (dependency.Argument.Length == 0) commonUnknown.Add("compiler:missing-command-line:" + dependency.Project);
                common["compiler:" + dependency.Project] = new("compiler:" + dependency.Project,
                    Digest(dependency.Argument.Select(argument => argument.Replace(root, "@repository", StringComparison.Ordinal))));
                foreach (var reason in compilationUnknown.GetValueOrDefault(dependency.Project) ?? []) commonUnknown.Add(reason);
                foreach (var source in dependency.Compile.Concat(dependency.Generated))
                {
                    var path = Relative(source);
                    if (!hashes.TryGetValue(path, out var input)) hashes[path] = input = new(path, CommonExecutionEvidence.Hash(source));
                    common["compile:" + path] = new("compile:" + path, input.Identity);
                }
            }
            var projectEdges = closure.SelectMany(item => item.ProjectReferences.Select(reference =>
                item.Project + " -> " + Relative(reference))).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
            var shared = new TestProjectInputs(project, common.Values.ToArray(), projectEdges, commonUnknown.ToArray(), "");
            shared = shared with { Identity = ProjectIdentity(shared) };
            projectInputs.Add(shared);
            foreach (var scope in projectScopes)
            {
                var unknown = new SortedSet<string>(scope.Unknown.Concat(shared.Unknown), StringComparer.Ordinal);
                var inputs = new SortedDictionary<string, ActionInput>(StringComparer.Ordinal);
                foreach (var path in scope.RuntimeInputs) BindInput(path, inputs, unknown, runtimeInput: true);
                var action = new TestAction(project, node.Properties["AssemblyName"], scope.Scope, scope.Methods,
                    inputs.Values.ToArray(), scope.Edges, unknown.ToArray(), shared.Identity, producer, environment, "");
                actions.Add(action with { Identity = Identity(action) });
            }
        }
        return new(2, candidate, projectInputs.ToArray(), actions.ToArray());

        void BindInput(string path, SortedDictionary<string, ActionInput> inputs, SortedSet<string> unknown, bool runtimeInput = false)
        {
            if (!hashes.TryGetValue(path, out var input))
            {
                var identity = runtimeInput && !System.IO.Path.IsPathFullyQualified(path) ? "unresolved-testhost-relative-path"
                    : File.Exists(System.IO.Path.GetFullPath(path, root)) ? CommonExecutionEvidence.Hash(System.IO.Path.GetFullPath(path, root)) : "absent";
                hashes[path] = input = new(path, identity);
            }
            inputs[path] = input;
            var owners = filemap?.Match(path) ?? [];
            if (owners.Length == 0) unknown.Add("filemap:unowned:" + path);
            else inputs["ownership:" + path] = new("ownership:" + path, Digest(owners.Select(owner =>
                $"{owner.Pattern}|{owner.Kind}|{owner.AdmissionPlane}|{owner.ProducedBy}|{string.Join(',', owner.ConsumedBy)}|{string.Join(',', owner.VerifiedBy)}|{owner.RuntimeDisposition}")));
        }

        string Relative(string path) => System.IO.Path.GetRelativePath(root, System.IO.Path.GetFullPath(path, root)).Replace('\\', '/');
    }

    private static IEnumerable<NativeProject> Closure(NativeProject node, NativeProject[] projects)
    {
        var pending = new Stack<NativeProject>(); pending.Push(node);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryPop(out var next))
        {
            if (!seen.Add(next.Project)) continue;
            yield return next;
            foreach (var reference in next.ProjectReferences)
            {
                var target = projects.Single(project => reference.Replace('\\', '/').EndsWith("/" + project.Project, StringComparison.Ordinal));
                pending.Push(target);
            }
        }
    }

    internal static string ProjectIdentity(TestProjectInputs project) => Digest(new[] { "test-project-v1", project.Project }
        .Concat(project.Inputs.Select(input => input.Path + "\0" + input.Identity)).Concat(project.Edges).Concat(project.Unknown));
    internal static string Identity(TestAction action) => Digest(new[] { "test-action-v2", action.Project, action.Assembly, action.Scope,
            action.ProjectIdentity, action.Producer, action.Environment }.Concat(action.Methods)
        .Concat(action.Inputs.Select(input => input.Path + "\0" + input.Identity)).Concat(action.Edges).Concat(action.Unknown));
    internal static void Validate(TestInputManifest plan)
    {
        if (plan.Version != 2 || plan.Projects.Any(project => project.Identity != ProjectIdentity(project))
            || plan.Projects.Select(project => project.Project).Distinct(StringComparer.Ordinal).Count() != plan.Projects.Length
            || plan.Actions.Any(action => action.Identity != Identity(action)
                || !plan.Projects.Any(project => project.Project == action.Project && project.Identity == action.ProjectIdentity))
            || plan.Actions.Select(action => (action.Project, action.Scope)).Distinct().Count() != plan.Actions.Length)
            throw new InvalidDataException("invalid test input manifest");
    }
    internal static string ProducerIdentity() => Digest(new[] { typeof(AffectedTestPlan).Assembly,
        typeof(ScribeExecutionDependencies).Assembly, typeof(Compilation).Assembly, typeof(CSharpCompilation).Assembly,
        typeof(Tomlyn.TomlSerializer).Assembly }.Select(assembly => assembly.ManifestModule.ModuleVersionId.ToString()));
    internal static string EnvironmentIdentity() => Digest(new[] { RuntimeInformation.RuntimeIdentifier, RuntimeInformation.FrameworkDescription,
        CultureInfo.CurrentCulture.Name, CultureInfo.CurrentUICulture.Name, "xunit-v2/vstest;configuration=Release;cwd=testhost;filter=class" }
        .Concat(Environment.GetEnvironmentVariables().Cast<System.Collections.DictionaryEntry>()
            .Where(entry => ((string)entry.Key).StartsWith("DOTNET_", StringComparison.Ordinal)
                || ((string)entry.Key).StartsWith("COMPlus_", StringComparison.Ordinal)
                || ((string)entry.Key).StartsWith("VSTEST_", StringComparison.Ordinal))
            .OrderBy(entry => (string)entry.Key, StringComparer.Ordinal).Select(entry => entry.Key + "=" + entry.Value)));
    internal static string Digest(IEnumerable<string> values)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        Span<byte> length = stackalloc byte[4];
        foreach (var value in values) { var bytes = Encoding.UTF8.GetBytes(value); BinaryPrimitives.WriteInt32LittleEndian(length, bytes.Length); hash.AppendData(length); hash.AppendData(bytes); }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}
