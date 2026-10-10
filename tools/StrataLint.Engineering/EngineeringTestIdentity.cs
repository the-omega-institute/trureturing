namespace StrataLint.Engineering;

internal static class EngineeringTestIdentity
{
    internal static string[] RequiredAssemblies(IReadOnlyList<EngineeringProjectRegistration> projects,
        string target, bool filtered)
    {
        if (projects.Where(project => project.IsTest).GroupBy(project => project.Assembly, StringComparer.OrdinalIgnoreCase)
            .Any(group => group.Count() != 1))
            throw new InvalidDataException("duplicate registered test assembly identity");
        if (projects.Where(project => project.IsTest).GroupBy(project => project.TestPartition, StringComparer.Ordinal)
            .Any(group => group.Count() != 1))
            throw new InvalidDataException("duplicate registered test partition");
        if (target == "tools/StrataLint.sln")
        {
            var owners = OwnerAssemblies(projects);
            if (owners.Length == 0) throw new InvalidDataException("list-test-owner-assemblies derived zero owner assemblies");
            return filtered ? [] : owners;
        }
        var selected = projects.SingleOrDefault(project => project.Path == target);
        if (selected is null || !selected.IsTest)
            throw new InvalidDataException("test target is not a registered test project: " + target);
        return [selected.Assembly];
    }

    internal static string[] OwnerAssemblies(IEnumerable<EngineeringProjectDeclaration> projects) =>
        projects.Where(project => project.Role == "owned-test").Select(project => project.Assembly)
            .Distinct(StringComparer.OrdinalIgnoreCase).Order(StringComparer.OrdinalIgnoreCase).ToArray();
}
