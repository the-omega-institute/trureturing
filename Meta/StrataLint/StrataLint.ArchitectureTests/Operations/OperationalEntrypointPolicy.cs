using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.ArchitectureTests;

internal sealed record OperationalEntrypointFinding(string Path, string Message);

internal static class OperationalEntrypointPolicy
{
    internal const string InventoryPath = ".fkst/operations.toml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static IReadOnlyList<OperationalEntrypointFinding> InspectRepository(
        string repositoryRoot)
    {
        var index = ReadIndex(repositoryRoot);
        var findings = new List<OperationalEntrypointFinding>();
        if (!index.TryGetValue(InventoryPath, out var inventoryMode))
        {
            return
            [
                new OperationalEntrypointFinding(
                    InventoryPath,
                    "operational inventory is absent from the git index"),
            ];
        }
        if (inventoryMode is not ("100644" or "100755"))
        {
            return
            [
                new OperationalEntrypointFinding(
                    InventoryPath,
                    $"operational inventory has non-regular git mode {inventoryMode}"),
            ];
        }

        var inventory = LoadInventory(Path.Combine(repositoryRoot, InventoryPath));
        findings.AddRange(InspectDeclaredArtifact(
            inventory.HostContractSchema,
            "host contract schema",
            index));
        findings.AddRange(InspectDeclaredArtifact(
            inventory.LauncherTemplate,
            "launcher template",
            index));
        var duplicateIds = inventory.Operations
            .GroupBy(static operation => operation.Id, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1)
            .Select(static group => group.Key)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var duplicate in inventory.Operations
                     .Where(operation => duplicateIds.Contains(operation.Id))
                     .GroupBy(static operation => operation.Id, StringComparer.Ordinal))
        {
            var implementations = duplicate
                .Select(static operation => operation.Implementation)
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();
            findings.Add(new OperationalEntrypointFinding(
                InventoryPath,
                implementations.Length > 1
                    ? $"operation id {duplicate.Key} is claimed by multiple tracked implementations: {string.Join(", ", implementations)}"
                    : $"duplicate operation id {duplicate.Key} repeats implementation {implementations[0]}"));
        }

        var makefile = File.ReadAllText(Path.Combine(repositoryRoot, "Makefile"));
        foreach (var operation in inventory.Operations.Where(operation => !duplicateIds.Contains(operation.Id)))
        {
            var implementationFindings = InspectImplementation(operation, index);
            findings.AddRange(implementationFindings);
            findings.AddRange(InspectTests(operation, index));
            if (implementationFindings.Count == 0)
            {
                findings.AddRange(InspectMakeTarget(operation, makefile));
            }
        }

        return findings;
    }

    private static IReadOnlyList<OperationalEntrypointFinding> InspectDeclaredArtifact(
        string path,
        string role,
        IReadOnlyDictionary<string, string> index)
    {
        if (IsHostLocal(path))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operational inventory declares a host-local path for {role}"),
            ];
        }
        if (!RepoPath.TryCreate(path, out _))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"declared {role} is not a canonical repository-relative path"),
            ];
        }
        if (!index.TryGetValue(path, out var mode))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"declared {role} is absent from the git index"),
            ];
        }
        if (mode == "120000")
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"declared {role} is a symlink (git mode 120000)"),
            ];
        }
        if (mode is not ("100644" or "100755"))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"declared {role} has non-regular git mode {mode}"),
            ];
        }

        return [];
    }

    private static IReadOnlyList<OperationalEntrypointFinding> InspectImplementation(
        Operation operation,
        IReadOnlyDictionary<string, string> index)
    {
        var path = operation.Implementation;
        if (IsAbsolute(path))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declares an absolute path"),
            ];
        }
        if (IsHostLocal(path))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declares a host-local path"),
            ];
        }
        if (!RepoPath.TryCreate(path, out _))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} implementation escapes the repository root or is not canonical"),
            ];
        }
        if (!index.TryGetValue(path, out var mode))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} implementation is absent from the git index"),
            ];
        }
        if (mode == "120000")
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} implementation is a symlink (git mode 120000)"),
            ];
        }
        if (mode is not ("100644" or "100755"))
        {
            return
            [
                new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} implementation has non-regular git mode {mode}"),
            ];
        }

        return [];
    }

    private static IReadOnlyList<OperationalEntrypointFinding> InspectTests(
        Operation operation,
        IReadOnlyDictionary<string, string> index)
    {
        var findings = new List<OperationalEntrypointFinding>();
        foreach (var path in operation.Tests)
        {
            if (IsHostLocal(path))
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declared test is a host-local path"));
            }
            else if (!RepoPath.TryCreate(path, out _))
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declared test is not a canonical repository-relative path"));
            }
            else if (!index.TryGetValue(path, out var mode))
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declared test is absent from the git index"));
            }
            else if (mode is not ("100644" or "100755"))
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    $"operation {operation.Id} declared test has non-regular git mode {mode}"));
            }
        }
        return findings;
    }

    private static IReadOnlyList<OperationalEntrypointFinding> InspectMakeTarget(
        Operation operation,
        string makefile)
    {
        var recipe = Recipe(makefile, operation.MakeTarget);
        var expected = $"@/bin/bash {operation.Implementation}";
        return string.Equals(recipe, expected, StringComparison.Ordinal)
            ? []
            :
            [
                new OperationalEntrypointFinding(
                    "Makefile",
                    $"make target {operation.MakeTarget} does not delegate exactly to {operation.Implementation}"),
            ];
    }

    private static string? Recipe(string makefile, string target)
    {
        var lines = makefile.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n');
        var targetIndex = Array.FindIndex(
            lines,
            line => string.Equals(line, target + ":", StringComparison.Ordinal));
        if (targetIndex < 0) return null;

        var recipe = lines
            .Skip(targetIndex + 1)
            .TakeWhile(static line => line.StartsWith('\t'))
            .Select(static line => line[1..])
            .ToArray();
        return recipe.Length == 1 ? recipe[0] : null;
    }

    private static bool IsAbsolute(string path) =>
        Path.IsPathFullyQualified(path)
        || path.StartsWith("/", StringComparison.Ordinal)
        || Regex.IsMatch(
            path,
            "^(?:[A-Za-z]:[\\\\/]|[\\\\/]{2})",
            RegexOptions.CultureInvariant,
            TimeSpan.FromSeconds(1));

    private static bool IsHostLocal(string path) =>
        IsAbsolute(path)
        || path.Equals("~", StringComparison.Ordinal)
        || path.StartsWith("~/", StringComparison.Ordinal)
        || path.StartsWith("~\\", StringComparison.Ordinal)
        || path.StartsWith("$HOME/", StringComparison.Ordinal)
        || path.StartsWith("${HOME}/", StringComparison.Ordinal)
        || path.StartsWith("%USERPROFILE%", StringComparison.OrdinalIgnoreCase);

    private static Inventory LoadInventory(string path)
    {
        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(File.ReadAllText(path))
                ?? throw new InvalidDataException("operational inventory is empty");
        }
        catch (TomlException exception)
        {
            throw new InvalidDataException("operational inventory is invalid TOML", exception);
        }

        if (!root.ContainsKey("host_contract_schema"))
        {
            throw new InvalidDataException(
                "operational inventory must declare host_contract_schema");
        }
        if (!root.ContainsKey("launcher_template"))
        {
            throw new InvalidDataException(
                "operational inventory must declare launcher_template");
        }
        RequireExactKeys(
            root,
            "inventory",
            "schema_version",
            "host_contract_schema",
            "launcher_template",
            "operations");
        if (!root.TryGetValue("schema_version", out var rawVersion)
            || rawVersion is not long version
            || version != 2)
        {
            throw new InvalidDataException("operational inventory schema_version must be 2");
        }
        if (!root.TryGetValue("operations", out var rawOperations)
            || rawOperations is not TomlTableArray tables
            || tables.Count == 0)
        {
            throw new InvalidDataException("operational inventory must declare operations");
        }

        return new Inventory(
            RequiredString(root, "host_contract_schema", "inventory"),
            RequiredString(root, "launcher_template", "inventory"),
            tables.Select((table, index) => ParseOperation(table, index)).ToArray());
    }

    private static Operation ParseOperation(TomlTable table, int index)
    {
        var location = $"operations[{index}]";
        RequireExactKeys(
            table,
            location,
            "id",
            "make_target",
            "implementation",
            "tests",
            "external_tools");
        var id = RequiredString(table, "id", location);
        var makeTarget = RequiredString(table, "make_target", location);
        var implementation = RequiredString(table, "implementation", location);
        var tests = RequiredStringArray(table, "tests", location);
        var externalTools = RequiredStringArray(table, "external_tools", location);
        if (!Regex.IsMatch(
                makeTarget,
                "^[a-z0-9][a-z0-9-]*$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1)))
        {
            throw new InvalidDataException($"{location}.make_target is not a literal Make target id");
        }
        if (tests.Distinct(StringComparer.Ordinal).Count() != tests.Length)
        {
            throw new InvalidDataException($"{location}.tests contains duplicate paths");
        }
        if (externalTools.Distinct(StringComparer.Ordinal).Count() != externalTools.Length
            || externalTools.Any(static tool => !Regex.IsMatch(
                tool,
                "^[a-z][a-z0-9.-]*$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1))))
        {
            throw new InvalidDataException(
                $"{location}.external_tools must contain unique literal tool ids");
        }
        return new Operation(id, makeTarget, implementation, tests, externalTools);
    }

    private static string RequiredString(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var raw) && raw is string { Length: > 0 } value
            ? value
            : throw new InvalidDataException($"{location}.{key} must be a non-empty string");

    private static string[] RequiredStringArray(TomlTable table, string key, string location)
    {
        if (!table.TryGetValue(key, out var raw)
            || raw is not TomlArray { Count: > 0 } array
            || array.Any(static item => item is not string { Length: > 0 }))
        {
            throw new InvalidDataException(
                $"{location}.{key} must be a non-empty string array");
        }
        return array.Cast<string>().ToArray();
    }

    private static void RequireExactKeys(
        TomlTable table,
        string location,
        params string[] expected)
    {
        var expectedKeys = expected.ToHashSet(StringComparer.Ordinal);
        var actualKeys = table.Keys.ToHashSet(StringComparer.Ordinal);
        if (!actualKeys.SetEquals(expectedKeys))
        {
            throw new InvalidDataException(
                $"{location} keys must be exactly: {string.Join(", ", expected)}");
        }
    }

    private static Dictionary<string, string> ReadIndex(string repositoryRoot)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            ["ls-files", "--stage", "-z"],
            repositoryRoot,
            TimeSpan.FromSeconds(120),
            64 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git ls-files --stage failed");
        }

        var entries = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var entry in SplitNul(result.StandardOutput))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0)
            {
                throw new InvalidOperationException("git index emitted invalid metadata");
            }
            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab)).Split(' ');
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length != 3 || metadata[2] != "0" || !entries.TryAdd(path, metadata[0]))
            {
                throw new InvalidOperationException(
                    $"unmerged or duplicate repository entry: {path}");
            }
        }
        return entries;
    }

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index <= bytes.Length; index++)
        {
            if (index != bytes.Length && bytes[index] != 0) continue;
            if (index > start) yield return bytes[start..index];
            start = index + 1;
        }
    }

    private sealed record Operation(
        string Id,
        string MakeTarget,
        string Implementation,
        IReadOnlyList<string> Tests,
        IReadOnlyList<string> ExternalTools);

    private sealed record Inventory(
        string HostContractSchema,
        string LauncherTemplate,
        IReadOnlyList<Operation> Operations);
}
