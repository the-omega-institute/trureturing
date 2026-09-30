using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

// These standalone validators survive removal of cross-stage evidence orchestration.
internal static class TestEvidenceCommands
{
    internal static int Run(IReadOnlyList<string> arguments, TextWriter output, TextWriter error)
    {
        try
        {
            if (arguments.FirstOrDefault() == "verify-trx")
            {
                try { return VerifyTrx(arguments.Skip(1).ToArray(), TestResultEvidence.Load, output); }
                catch (Exception exception) { error.WriteLine($"TEST_EVIDENCE_FAILED {exception.Message}"); return 2; }
            }
            if (arguments.FirstOrDefault() == "list-test-owner-assemblies")
            {
                foreach (var assembly in TestOwnerAssemblies(arguments.Skip(1).ToArray())) output.WriteLine(assembly);
                return 0;
            }
            throw new ArgumentException("expected verify-trx or list-test-owner-assemblies");
        }
        catch (Exception exception)
        {
            error.WriteLine("ENGINEERING_TEST_PLAN_FAILED " + exception.Message);
            return 2;
        }
    }

    internal static IReadOnlyList<string> TestOwnerAssemblies(IReadOnlyList<string> arguments)
    {
        string? root = null, target = null;
        bool? filtered = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw new ArgumentException("test target options must be name/value pairs");
            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--repository" when root is null && !string.IsNullOrWhiteSpace(value): root = Path.GetFullPath(value); break;
                case "--target" when target is null && !string.IsNullOrWhiteSpace(value): target = Path.GetFullPath(value); break;
                case "--filtered" when filtered is null && value is "true" or "false": filtered = value == "true"; break;
                default: throw new ArgumentException("invalid test target option: " + arguments[index]);
            }
        }
        if (root is null || target is null || filtered is null)
            throw new ArgumentException("test target requires --repository, --target, and --filtered");
        var relative = Path.GetRelativePath(root, target).Replace('\\', '/');
        if (relative == ".." || relative.StartsWith("../", StringComparison.Ordinal) || Path.IsPathRooted(relative))
            throw new InvalidDataException("test target is outside repository: " + target);
        var projects = RepositoryRules.ReadTrackedProjects(root);
        if (relative == "tools/StrataLint.sln")
        {
            var owners = RepositoryRules.CalculateOwnerAssemblies(projects);
            if (owners.Length == 0) throw new InvalidDataException("list-test-owner-assemblies derived zero owner assemblies");
            return filtered.Value ? [] : owners;
        }
        var selected = projects.Projects.SingleOrDefault(project => project.Path == relative)?.Registration;
        if (selected is null || !selected.IsTest)
            throw new InvalidDataException("test target is not a registered test project: " + relative);
        return [selected.Assembly];
    }

    internal static int VerifyTrx(IReadOnlyList<string> arguments, Func<string, TestResultEvidence> load, TextWriter output)
    {
        string? directory = null;
        var required = new List<string>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw new ArgumentException("verify-trx options must be --name value pairs");
            switch (arguments[index])
            {
                case "--results-directory" when directory is null: directory = arguments[index + 1]; break;
                case "--required-assembly" when !string.IsNullOrWhiteSpace(arguments[index + 1]): required.Add(arguments[index + 1]); break;
                default: throw new ArgumentException($"unknown verify-trx option: {arguments[index]}");
            }
        }
        if (string.IsNullOrWhiteSpace(directory)) throw new ArgumentException("--results-directory is required");
        var evidence = load(Path.GetFullPath(directory));
        foreach (var assembly in required)
        {
            var count = evidence.CountAssembly(assembly);
            if (count == 0) throw new InvalidDataException($"TRX has no executed identity from required assembly {assembly}");
            output.WriteLine($"TEST_ASSEMBLY_EVIDENCE_ACCEPTED assembly={assembly} evidence=trx executed={count}");
        }
        if (required.Count == 0) output.WriteLine($"TEST_EVIDENCE_ACCEPTED evidence=trx executed={evidence.Executed}");
        return 0;
    }
}
