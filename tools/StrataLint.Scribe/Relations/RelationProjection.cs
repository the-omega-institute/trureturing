using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace StrataLint.Scribe;

public sealed record RelationEdge(string Kind, string TargetKind, string Target, string? DescribeId);
public sealed record RelationClaim(string Problem, string Resolution, ImmutableArray<string> Members);
public sealed record RelationDescribe(
    string Id, string KindSource, string? Kind, string? Role, string? Declaration, RelationClaim? Claim);

/// <summary>Order-free relations retain the multiplicity of every authored occurrence.</summary>
public sealed record RelationProjection(
    string Gid,
    string SourcePath,
    ImmutableArray<RelationEdge> Edges,
    ImmutableArray<string> InlineReferences,
    ImmutableArray<RelationDescribe> Describes)
{
    public static RelationProjection FromDefinition(DocumentDefinition definition)
    {
        ArgumentNullException.ThrowIfNull(definition);
        var document = definition.Document;
        var references = ImmutableArray.CreateBuilder<string>();
        var describes = ImmutableArray.CreateBuilder<RelationDescribe>();
        void Visit(BlockSequence blocks)
        {
            foreach (var block in blocks.Items)
            {
                switch (block)
                {
                    case DocumentBlock.Paragraph paragraph:
                        references.AddRange(paragraph.Content.Items.OfType<Inline.GidReference>()
                            .Select(static inline => inline.Reference.Value));
                        break;
                    case DocumentBlock.Section section:
                        Visit(section.Content);
                        break;
                    case DocumentBlock.Describe describe:
                        var declaration = (describe.Statement as DescribeStatement.LeanDeclaration)?.Value.Value;
                        var derived = describe.KindSource as DescribeKindSource.ReportDerived;
                        var authored = describe.KindSource as DescribeKindSource.Authored;
                        var claim = describe.OpenProblemResolutionClaim;
                        describes.Add(new(describe.Id.Value, derived is null ? "authored" : "report-derived",
                            authored?.Value.ToString(), derived?.Role?.ToString(), declaration,
                            claim is null ? null : new(claim.ProblemSlug.Value, claim.ResolutionKind.ToString(),
                                claim.Members(declaration ?? string.Empty).Order(StringComparer.Ordinal).ToImmutableArray())));
                        Visit(describe.Content);
                        break;
                }
            }
        }
        Visit(document.Content);
        return new(document.Header.Gid.Value, NormalizeSource(definition.SourcePath),
            document.Edges.Select(Edge).ToImmutableArray(), references.ToImmutable(), describes.ToImmutable());
    }

    private static RelationEdge Edge(DocumentEdge edge) => edge switch
    {
        DocumentEdge.Dependency dependency => new("dependency", "document", dependency.Target.Value, null),
        DocumentEdge.TruthAnchor truth => new("truth", "declaration", truth.Target.Value, truth.DescribeId?.Value),
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document target } =>
            new("narrative", "document", target.DocumentGid.Value, null),
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe target } =>
            new("narrative", "describe", target.DocumentGid.Value, target.DescribeId.Value),
        _ => throw new InvalidOperationException("Unknown relation edge."),
    };

    internal static string NormalizeSource(string path)
    {
        var normalized = path.Replace('\\', '/');
        var marker = normalized.LastIndexOf("/Blueprint/", StringComparison.Ordinal);
        return marker < 0 ? normalized : normalized[(marker + 1)..];
    }

    internal ImmutableArray<string> CanonicalItems() =>
    [
        "gid:" + JsonSerializer.Serialize(Gid),
        "path:" + JsonSerializer.Serialize(SourcePath),
        .. Edges.Select(static edge => "edge:" + JsonSerializer.Serialize(edge)).Order(StringComparer.Ordinal),
        .. InlineReferences.Select(static reference => "inline:" + JsonSerializer.Serialize(reference)).Order(StringComparer.Ordinal),
        .. Describes.Select(static describe => "describe:" + JsonSerializer.Serialize(describe with
        {
            Claim = describe.Claim is null ? null : describe.Claim with
            {
                Members = describe.Claim.Members.Order(StringComparer.Ordinal).ToImmutableArray(),
            },
        })).Order(StringComparer.Ordinal),
    ];

    public byte[] Encode() => Encoding.UTF8.GetBytes(JsonSerializer.Serialize(CanonicalItems()));

    public string? FirstDifference(RelationProjection other)
    {
        var left = CanonicalItems();
        var right = other.CanonicalItems();
        for (var index = 0; index < Math.Max(left.Length, right.Length); index++)
        {
            var a = index < left.Length ? left[index] : "<missing>";
            var b = index < right.Length ? right[index] : "<missing>";
            if (!string.Equals(a, b, StringComparison.Ordinal)) return $"static={a}; executed={b}";
        }
        return null;
    }
}
