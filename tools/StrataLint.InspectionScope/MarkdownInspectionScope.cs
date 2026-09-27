using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record RegisteredMarkdownScope(string[] WholeTreeInputs, string[] ChangedInputs);

// The complete plan retains both endpoints of deletions and renames. Scribe
// owns source-to-projection mapping; selection here uses only registered globs.
internal sealed record MarkdownInspectionScope(bool WholeTree, string[] Paths)
{
    internal static MarkdownInspectionScope Select(RegisteredMarkdownScope? registration,
        IReadOnlyCollection<string>? changes, IReadOnlyCollection<string> inventory, string[] wholeTreePaths)
    {
        if (changes is null) return Whole();
        if (registration is null) throw new InvalidDataException("missing scribe-markdown path scope registration");
        Validate(registration);
        if (changes.Any(path => !RepoPath.TryCreate(path, out _)))
            throw new InvalidDataException("invalid scribe-markdown changed path");
        var global = registration.WholeTreeInputs.Select(FileMapGlob.Create).ToArray();
        if (changes.Any(path => global.Any(pattern => pattern.IsMatch(path)))) return Whole();
        var local = registration.ChangedInputs.Select(FileMapGlob.Create).ToArray();
        return new(false, changes.Where(path => local.Any(pattern => pattern.IsMatch(path)))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray());

        MarkdownInspectionScope Whole() => new(true,
            EngineeringProjectRegistry.ExpandInputs(inventory, wholeTreePaths, [], "scribe-markdown").ToArray());
    }

    internal static void Validate(RegisteredMarkdownScope registration)
    {
        foreach (var patterns in new[] { registration.WholeTreeInputs, registration.ChangedInputs })
        {
            if (patterns is null || patterns.Length == 0 || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
                throw new InvalidDataException("empty or duplicate scribe-markdown path scope patterns");
            foreach (var pattern in patterns) _ = FileMapGlob.Create(pattern);
        }
    }
}
