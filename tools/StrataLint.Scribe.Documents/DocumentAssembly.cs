using System.Collections.Immutable;
using System.Reflection;

namespace StrataLint.Scribe.Documents;

public static class DocumentAssembly
{
    public static Assembly Value { get; } = typeof(DocumentAssembly).Assembly;

    public static ImmutableArray<DocumentDefinition> Definitions { get; } =
        DocumentDefinitions.Discover(Value);
}
