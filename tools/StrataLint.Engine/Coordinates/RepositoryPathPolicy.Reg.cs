namespace StrataLint.Engine;

internal static partial class RepositoryPathPolicy
{
    private static bool IsDeclarationSourcePath(string value, ValidatedPolicy policy)
    {
        if (!value.EndsWith(".lean", StringComparison.Ordinal)) return false;
        if (value.StartsWith("Reg/D5/", StringComparison.Ordinal))
        {
            var suffix = RepoPath.CreateKnown(value["Reg/".Length..]);
            if (!TryResolve(suffix, out var gid) || gid?.ToTarget() is not Target.Formal
                || Validate(suffix, policy) is not null) return false;
            // Formal GID grammar checks strata and segment shape; SL-011's existing
            // controlled-domain relation also applies to a declaration owner suffix.
            var parts = suffix.Value.Split('/');
            return parts[1].StartsWith("X_", StringComparison.Ordinal)
                || HasControlledDomain(suffix, policy);
        }

        if (!value.StartsWith("Reg/Support/", StringComparison.Ordinal)
            && !value.StartsWith("Reg/Catalogs/", StringComparison.Ordinal)) return false;
        var segments = value[..^5].Split('/');
        return segments.Length >= 3 && segments.Skip(2).All(CamelPattern.IsMatch);
    }
}
