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

    internal static IReadOnlyList<string> EnumerateRepositoryLaunchdMembership(
        string repositoryRoot)
    {
        var index = ReadIndex(repositoryRoot);
        var inventory = LoadInventory(Path.Combine(repositoryRoot, InventoryPath));
        var makefile = File.ReadAllText(Path.Combine(repositoryRoot, "Makefile"));
        var discovery = DiscoverLaunchdUnits(
            repositoryRoot,
            inventory.Operations,
            index.Keys,
            makefile);
        var units = discovery.Units.Order(StringComparer.Ordinal).ToArray();
        if (units.Length == 0)
        {
            throw new InvalidDataException(
                "repository launchd membership source returned no launchd units");
        }
        return units;
    }

    internal static IReadOnlyList<OperationalEntrypointFinding> InspectRepository(
        string repositoryRoot,
        IEnumerable<string> operationalLaunchdMembership)
    {
        ArgumentNullException.ThrowIfNull(operationalLaunchdMembership);
        var operationalUnits = operationalLaunchdMembership.ToHashSet(StringComparer.Ordinal);
        if (operationalUnits.Any(static id => !Regex.IsMatch(
                id,
                "^[a-z0-9][a-z0-9-]*$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1))))
        {
            throw new InvalidDataException(
                "operational launchd membership must contain canonical logical unit ids");
        }

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
        findings.AddRange(InspectLaunchdUnits(
            repositoryRoot,
            inventory,
            duplicateIds,
            index,
            makefile,
            operationalUnits));
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

    private static IReadOnlyList<OperationalEntrypointFinding> InspectLaunchdUnits(
        string repositoryRoot,
        Inventory inventory,
        IReadOnlySet<string> duplicateOperationIds,
        IReadOnlyDictionary<string, string> index,
        string makefile,
        IReadOnlySet<string> operationalUnits)
    {
        var findings = new List<OperationalEntrypointFinding>();
        var declaredUnits = inventory.LaunchdUnits.ToHashSet(StringComparer.Ordinal);
        var discovery = DiscoverLaunchdUnits(
            repositoryRoot,
            inventory.Operations,
            index.Keys,
            makefile);
        findings.AddRange(discovery.Findings);
        foreach (var id in operationalUnits.Except(declaredUnits, StringComparer.Ordinal).Order())
        {
            findings.Add(new OperationalEntrypointFinding(
                InventoryPath,
                $"operational launchd unit {id} is absent from operational inventory"));
        }
        foreach (var id in discovery.Units
                     .Except(operationalUnits, StringComparer.Ordinal)
                     .Except(declaredUnits, StringComparer.Ordinal)
                     .Order())
        {
            findings.Add(new OperationalEntrypointFinding(
                InventoryPath,
                $"launchd unit {id} is absent from operational inventory"));
        }

        var operations = inventory.Operations
            .Where(operation => !duplicateOperationIds.Contains(operation.Id))
            .ToDictionary(static operation => operation.Id, StringComparer.Ordinal);
        foreach (var id in inventory.LaunchdUnits)
        {
            findings.AddRange(InspectDeclaredArtifact(
                $".fkst/launchd/{id}.plist.in",
                $"launchd unit {id} template",
                index));
            findings.AddRange(InspectLaunchdOperation(
                id,
                "render",
                $".fkst/scripts/render-{id}-launcher.sh",
                operations));
            findings.AddRange(InspectLaunchdOperation(
                id,
                "check",
                $".fkst/scripts/check-{id}-launcher.sh",
                operations));
        }

        return findings;
    }

    private static IReadOnlyList<OperationalEntrypointFinding> InspectLaunchdOperation(
        string unitId,
        string role,
        string expectedImplementation,
        IReadOnlyDictionary<string, Operation> operations)
    {
        var expectedId = $"{unitId}-launcher-{role}";
        if (!operations.TryGetValue(expectedId, out var operation))
        {
            return
            [
                new OperationalEntrypointFinding(
                    InventoryPath,
                    $"launchd unit {unitId} has no {role} operation {expectedId}"),
            ];
        }

        var findings = new List<OperationalEntrypointFinding>();
        if (!string.Equals(operation.MakeTarget, expectedId, StringComparison.Ordinal))
        {
            findings.Add(new OperationalEntrypointFinding(
                InventoryPath,
                $"launchd unit {unitId} {role} operation must use make target {expectedId}"));
        }
        if (!string.Equals(operation.Implementation, expectedImplementation, StringComparison.Ordinal))
        {
            findings.Add(new OperationalEntrypointFinding(
                InventoryPath,
                $"launchd unit {unitId} {role} operation must use implementation {expectedImplementation}"));
        }
        return findings;
    }

    private static LaunchdDiscovery DiscoverLaunchdUnits(
        string repositoryRoot,
        IReadOnlyList<Operation> operations,
        IEnumerable<string> indexedPaths,
        string makefile)
    {
        var units = new HashSet<string>(StringComparer.Ordinal);
        var launchdCandidates = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in indexedPaths)
        {
            AddLaunchdCandidate(path, launchdCandidates);
            AddLaunchdUnitFromScriptPath(path, units);
        }

        foreach (var relativeDirectory in new[] { ".fkst/launchd", ".fkst/scripts" })
        {
            var directory = Path.Combine(
                repositoryRoot,
                relativeDirectory.Replace('/', Path.DirectorySeparatorChar));
            if (!Directory.Exists(directory)) continue;
            var searchOption = string.Equals(
                relativeDirectory,
                ".fkst/launchd",
                StringComparison.Ordinal)
                ? SearchOption.AllDirectories
                : SearchOption.TopDirectoryOnly;
            foreach (var path in Directory.EnumerateFiles(directory, "*", searchOption))
            {
                var pathWithinDirectory = Path.GetRelativePath(directory, path)
                    .Replace(Path.DirectorySeparatorChar, '/');
                var relativePath = $"{relativeDirectory}/{pathWithinDirectory}";
                AddLaunchdCandidate(relativePath, launchdCandidates);
                AddLaunchdUnitFromScriptPath(relativePath, units);
            }
        }

        var findings = new List<OperationalEntrypointFinding>();
        var candidatePathsByUnit = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var path in launchdCandidates.Order(StringComparer.Ordinal))
        {
            var match = Regex.Match(
                path,
                @"^\.fkst/launchd/([a-z0-9][a-z0-9-]*)\.plist(?:\.in)?$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1));
            if (match.Success)
            {
                var id = match.Groups[1].Value;
                units.Add(id);
                if (!candidatePathsByUnit.TryGetValue(id, out var paths))
                {
                    paths = [];
                    candidatePathsByUnit.Add(id, paths);
                }
                paths.Add(path);
            }
            else
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    "noncanonical launchd entry; expected <unit-id>.plist or <unit-id>.plist.in"));
            }
        }
        foreach (var (id, paths) in candidatePathsByUnit.Where(static item => item.Value.Count > 1))
        {
            var canonicalTemplate = $".fkst/launchd/{id}.plist.in";
            foreach (var path in paths.Where(path => !string.Equals(
                         path,
                         canonicalTemplate,
                         StringComparison.Ordinal)))
            {
                findings.Add(new OperationalEntrypointFinding(
                    path,
                    $"additional launchd path for unit {id}; canonical template is {canonicalTemplate}"));
            }
        }

        foreach (var operation in operations)
        {
            AddLaunchdUnitFromOperationId(operation.Id, units);
        }
        foreach (var line in makefile.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n'))
        {
            var match = Regex.Match(
                line,
                "^([a-z0-9][a-z0-9-]*)-launcher-(?:render|check):$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1));
            if (match.Success) units.Add(match.Groups[1].Value);
        }
        return new LaunchdDiscovery(units, findings);
    }

    private static void AddLaunchdCandidate(string path, ISet<string> candidates)
    {
        if (path.StartsWith(".fkst/launchd/", StringComparison.Ordinal))
        {
            candidates.Add(path);
        }
    }

    private static void AddLaunchdUnitFromScriptPath(string path, ISet<string> units)
    {
        var match = Regex.Match(
            path,
            @"^\.fkst/scripts/(?:render|check)-([a-z0-9][a-z0-9-]*)-launcher\.sh$",
            RegexOptions.CultureInvariant,
            TimeSpan.FromSeconds(1));
        if (match.Success) units.Add(match.Groups[1].Value);
    }

    private static void AddLaunchdUnitFromOperationId(string id, ISet<string> units)
    {
        var match = Regex.Match(
            id,
            "^([a-z0-9][a-z0-9-]*)-launcher-(?:render|check)$",
            RegexOptions.CultureInvariant,
            TimeSpan.FromSeconds(1));
        if (match.Success) units.Add(match.Groups[1].Value);
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
        if (!root.ContainsKey("launchd_units"))
        {
            throw new InvalidDataException(
                "operational inventory must declare launchd_units");
        }
        RequireExactKeys(
            root,
            "inventory",
            "schema_version",
            "host_contract_schema",
            "launchd_units",
            "operations");
        if (!root.TryGetValue("schema_version", out var rawVersion)
            || rawVersion is not long version
            || version != 3)
        {
            throw new InvalidDataException("operational inventory schema_version must be 3");
        }
        if (!root.TryGetValue("operations", out var rawOperations)
            || rawOperations is not TomlTableArray tables
            || tables.Count == 0)
        {
            throw new InvalidDataException("operational inventory must declare operations");
        }

        var launchdUnits = RequiredStringArrayAllowEmpty(root, "launchd_units", "inventory");
        if (launchdUnits.Distinct(StringComparer.Ordinal).Count() != launchdUnits.Length
            || launchdUnits.Any(static id => !Regex.IsMatch(
                id,
                "^[a-z0-9][a-z0-9-]*$",
                RegexOptions.CultureInvariant,
                TimeSpan.FromSeconds(1))))
        {
            throw new InvalidDataException(
                "inventory.launchd_units must contain unique literal unit ids");
        }

        return new Inventory(
            RequiredString(root, "host_contract_schema", "inventory"),
            launchdUnits,
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

    private static string[] RequiredStringArrayAllowEmpty(
        TomlTable table,
        string key,
        string location)
    {
        if (!table.TryGetValue(key, out var raw)
            || raw is not TomlArray array
            || array.Any(static item => item is not string { Length: > 0 }))
        {
            throw new InvalidDataException(
                $"{location}.{key} must be a string array");
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

    private sealed record LaunchdDiscovery(
        IReadOnlySet<string> Units,
        IReadOnlyList<OperationalEntrypointFinding> Findings);

    private sealed record Inventory(
        string HostContractSchema,
        IReadOnlyList<string> LaunchdUnits,
        IReadOnlyList<Operation> Operations);
}
