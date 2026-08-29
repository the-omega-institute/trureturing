using System.Reflection;

namespace StrataLint.ArchitectureTests;

internal static class CapabilityPolicy
{
    private static readonly HashSet<string> CapabilityOutcomeNames =
        ["Accepted", "Admitted", "Clear", "Completed", "ProtectedSurfaceChange"];

    internal static string[] EnumerateNames(Assembly assembly) =>
        assembly.GetExportedTypes()
            .Where(IsCapabilitySemanticType)
            .Select(static type => type.FullName
                ?? throw new InvalidOperationException("Capability type has no full name."))
            .Order(StringComparer.Ordinal)
            .ToArray();

    internal static string[] PubliclyConstructible(IEnumerable<Type> types) =>
        types.Where(IsCapabilitySemanticType)
            .Where(static type => type.GetConstructors(
                    BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
                .Any(static constructor =>
                    constructor.IsPublic
                    || constructor.IsFamily
                    || constructor.IsFamilyOrAssembly))
            .Select(static type => type.FullName ?? type.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

    internal static bool IsCapabilitySemanticType(Type type)
    {
        if (!type.IsNested)
        {
            return IsTopLevelCapability(type);
        }

        return CapabilityOutcomeNames.Contains(type.Name)
            && type.GetProperties(BindingFlags.Instance | BindingFlags.Public)
                .Any(static property => IsTopLevelCapability(property.PropertyType));
    }

    private static bool IsTopLevelCapability(Type type) =>
        !type.IsNested
        && (type.Name.EndsWith("Certificate", StringComparison.Ordinal)
            || type.Name.EndsWith("Clear", StringComparison.Ordinal)
            || type.Name.StartsWith("Accepted", StringComparison.Ordinal)
            || type.Name.StartsWith("Validated", StringComparison.Ordinal)
            || type.Name is "CanonicalFixedPoint"
                or "CompletedRuleSet"
                or "FrozenLedgerConsistent"
                or "FrozenMaterialCatalog"
                or "RevocationPlan"
                or "TrustedRevocationReceiptStore");
}
