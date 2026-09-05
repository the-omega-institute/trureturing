using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal static class ReportDerivedDeclarationFixture
{
    internal static LeanDeclaration Declaration(string name, string kind) =>
        new(name, kind, "Nat = Nat", ImmutableArray<string>.Empty);
}
