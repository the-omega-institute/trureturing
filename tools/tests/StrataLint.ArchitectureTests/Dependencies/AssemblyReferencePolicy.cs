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

    internal static string[] ApplicationReferences(Assembly assembly) =>
        NonPlatformReferences(assembly)
            .Where(static name =>
                name == "StrataLint"
                || name.StartsWith("StrataLint.", StringComparison.Ordinal))
            .ToArray();

    // Platform means "ships inside the Microsoft.NETCore.App shared framework", not
    // "starts with System.". Microsoft.Win32.Primitives sits in that same runtime
    // directory as System.ComponentModel.Primitives and needs no PackageReference, so a
    // System.-prefix-only test misreports it as a third-party dependency. Named exactly
    // rather than by a Microsoft.Win32. prefix: Microsoft.Win32.Registry is a NuGet
    // package and must keep failing this check.
    private static bool IsPlatformAssembly(string name) =>
        name is "System" or "mscorlib" or "netstandard" or "Microsoft.CSharp"
            or "Microsoft.Win32.Primitives"
        || name.StartsWith("System.", StringComparison.Ordinal);
}
