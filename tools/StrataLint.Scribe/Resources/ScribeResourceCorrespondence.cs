using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record ScribeResourceDifference(
    string DefinitionPath, string InputPath, string? RecordedSha256, string? CurrentSha256)
{
    public override string ToString() =>
        $"{DefinitionPath}: input={InputPath} recorded={RecordedSha256 ?? "missing"} current={CurrentSha256 ?? "missing"}";
}

public sealed record ScribeResourceCorrespondenceResult(
    int ConsistentCount,
    ImmutableArray<ScribeResourceDifference> InputsChanged,
    ImmutableArray<ScribeResourceDifference> PackOnly,
    ImmutableArray<ScribeResourceDifference> DiskOnly)
{
    public bool IsCorresponding => InputsChanged.IsEmpty && PackOnly.IsEmpty && DiskOnly.IsEmpty;
}

/// <summary>Compares every recorded definition input with a file view without executing definitions.</summary>
public static class ScribeResourceCorrespondence
{
    public static ScribeResourceCorrespondenceResult Compare(ScribeResourcePack pack, string repositoryRoot) =>
        Compare(pack, new WorkingTreeScribeResourceFileView(repositoryRoot));

    public static ScribeResourceCorrespondenceResult Compare(ScribeResourcePack pack, IScribeResourceFileView files)
    {
        ArgumentNullException.ThrowIfNull(pack);
        ArgumentNullException.ThrowIfNull(files);
        var current = files.EnumerateDefinitionPaths().ToHashSet(StringComparer.Ordinal);
        var consistent = 0;
        var changed = ImmutableArray.CreateBuilder<ScribeResourceDifference>();
        var packOnly = ImmutableArray.CreateBuilder<ScribeResourceDifference>();
        foreach (var entry in pack.Manifest.Entries)
        {
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(entry.Gid);
            var entryInput = entry.Inputs.SingleOrDefault(input => input.Path == definitionPath && input.Sha256 is not null)
                ?? throw new ScribeResourcePackException(ScribeResourcePackErrorCode.InvalidManifest,
                    $"Definition input is missing: {definitionPath}.");
            if (!current.Remove(definitionPath))
            {
                packOnly.Add(new ScribeResourceDifference(definitionPath, definitionPath, entryInput.Sha256, null));
                continue;
            }
            ScribeResourceDifference? difference = null;
            foreach (var input in entry.Inputs)
            {
                var digest = ReadDigest(files, input.Path);
                if (input.Sha256 == digest) continue;
                difference = new ScribeResourceDifference(definitionPath, input.Path, input.Sha256, digest);
                break;
            }
            if (difference is null) consistent++;
            else changed.Add(difference);
        }
        var diskOnly = current.Order(StringComparer.Ordinal)
            .Select(path => new ScribeResourceDifference(path, path, null, ReadDigest(files, path)))
            .ToImmutableArray();
        return new ScribeResourceCorrespondenceResult(consistent, changed.ToImmutable(), packOnly.ToImmutable(), diskOnly);
    }

    private static string? ReadDigest(IScribeResourceFileView files, string relativePath)
    {
        var bytes = files.ReadBytes(relativePath);
        return bytes is { } content ? ScribeResourcePack.Digest(content.ToArray()) : null;
    }
}
