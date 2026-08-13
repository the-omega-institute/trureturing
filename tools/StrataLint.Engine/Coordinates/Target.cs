using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

internal sealed class CoordinatePath : IEquatable<CoordinatePath>
{
    private CoordinatePath(ImmutableArray<string> values) => Values = values;

    internal ImmutableArray<string> Values { get; }

    internal static CoordinatePath Create(IEnumerable<string> values) =>
        new(values.ToImmutableArray());

    public bool Equals(CoordinatePath? other) =>
        other is not null && Values.SequenceEqual(other.Values, StringComparer.Ordinal);

    public override bool Equals(object? obj) => obj is CoordinatePath other && Equals(other);

    public override int GetHashCode()
    {
        var hash = new HashCode();
        foreach (var value in Values)
        {
            hash.Add(value, StringComparer.Ordinal);
        }

        return hash.ToHashCode();
    }
}

[Union(EnableImplicitConversions = false)]
internal partial record Target
{
    public partial record Formal(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path,
        string? Declaration);

    public partial record Blueprint(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path);

    public partial record Evidence(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path,
        string Selector,
        ArtifactKindId ArtifactKind);

    public partial record Chronicle(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path);

    public partial record Library(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path);

    public partial record Paper(
        string Theory,
        CoordinatePath Coordinates,
        RepoPath Path,
        bool Frozen);
}
