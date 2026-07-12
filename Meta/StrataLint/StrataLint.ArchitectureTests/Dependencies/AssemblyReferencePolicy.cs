using System.Reflection;

namespace StrataLint.ArchitectureTests;

internal static class AssemblyReferencePolicy
{
    internal static string[] NonPlatformReferences(Assembly assembly) =>
        assembly.GetReferencedAssemblies()
            .Select(static reference => reference.Name
                ?? throw new InvalidOperationException("Assembly reference has no name."))
            .Where(static name => !IsPlatformAssembly(name))
            .Order(StringComparer.Ordinal)
            .ToArray();

    internal static string[] UnexpectedReferences(
        Assembly assembly,
        params string[] allowedNonPlatformReferences)
    {
        var allowed = allowedNonPlatformReferences.ToHashSet(StringComparer.Ordinal);
        return NonPlatformReferences(assembly)
            .Where(reference => !allowed.Contains(reference))
            .ToArray();
    }

    internal static string[] ApplicationReferences(Assembly assembly) =>
        NonPlatformReferences(assembly)
            .Where(static name =>
                name == "StrataLint"
                || name.StartsWith("StrataLint.", StringComparison.Ordinal))
            .ToArray();

    private static bool IsPlatformAssembly(string name) =>
        name is "System" or "mscorlib" or "netstandard" or "Microsoft.CSharp"
        || name.StartsWith("System.", StringComparison.Ordinal);
}
