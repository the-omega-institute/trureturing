using System.Collections.Immutable;
using System.Diagnostics.CodeAnalysis;
using System.Text.RegularExpressions;
using Pidgin;
using static Pidgin.Parser<char>;

namespace StrataLint.Engine;

public sealed class Gid : IEquatable<Gid>
{
    private const string Theory = "D5";
    private const string TagSeparator = "--";

    private static readonly Parser<char, string> SurfaceParser = Any
        .Where(static character =>
            character is >= 'A' and <= 'Z'
                or >= 'a' and <= 'z'
                or >= '0' and <= '9'
                or '_'
                or '/'
                or '.'
                or '-')
        .AtLeastOnceString()
        .Before(End);

    private static readonly Regex CamelPattern = new(
        "^[A-Z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex DeclarationPattern = new(
        "^[A-Za-z_][A-Za-z0-9_]*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex SafeSegmentPattern = new(
        "^[A-Za-z0-9_.-]+$",
        RegexOptions.CultureInvariant);

    private static readonly Regex DatePattern = new(
        "^[0-9]{4}-[0-9]{2}-[0-9]{2}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex PaperPattern = new(
        "^D5-P[0-9]{3}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex ExperimentPattern = new(
        "^D5-X[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private readonly Target target;

    private Gid(string value, Target target)
    {
        Value = value;
        this.target = target;
    }

    public string Value { get; }

    public RepoPath Path => target switch
    {
        Target.Formal formal => formal.Path,
        Target.Blueprint blueprint => blueprint.Path,
        Target.Evidence evidence => evidence.Path,
        Target.Chronicle chronicle => chronicle.Path,
        Target.Library library => library.Path,
        Target.Paper paper => paper.Path,
    };

    public static bool TryParse(string? value, [NotNullWhen(true)] out Gid? gid)
    {
        if (value is null)
        {
            gid = null;
            return false;
        }

        try
        {
            var surface = SurfaceParser.ParseOrThrow(value);
            var parsedTarget = ParseTarget(surface);
            if (!string.Equals(Print(parsedTarget), surface, StringComparison.Ordinal))
            {
                gid = null;
                return false;
            }

            gid = new Gid(surface, parsedTarget);
            return true;
        }
        catch (Exception exception) when (exception is ParseException or FormatException or ArgumentException)
        {
            gid = null;
            return false;
        }
    }

    internal Target ToTarget() => target;

    internal static Gid FromTarget(Target target)
    {
        var surface = Print(target);
        if (!TryParse(surface, out var gid) || !Equals(gid.target, target))
        {
            throw new InvalidOperationException("Target does not have a canonical GID inverse.");
        }

        return gid;
    }

    public bool Equals(Gid? other) =>
        other is not null && string.Equals(Value, other.Value, StringComparison.Ordinal);

    public override bool Equals(object? obj) => obj is Gid other && Equals(other);

    public override int GetHashCode() => StringComparer.Ordinal.GetHashCode(Value);

    public override string ToString() => Value;

    private static Target ParseTarget(string surface)
    {
        var tagIndex = surface.IndexOf(TagSeparator, StringComparison.Ordinal);
        if (tagIndex >= 0
            && surface.IndexOf(TagSeparator, tagIndex + TagSeparator.Length, StringComparison.Ordinal) >= 0)
        {
            throw new FormatException("GID contains more than one tag separator.");
        }

        var basePart = tagIndex < 0 ? surface : surface[..tagIndex];
        var tag = tagIndex < 0 ? null : surface[(tagIndex + TagSeparator.Length)..];
        if (tag is { Length: 0 })
        {
            throw new FormatException("GID tag is empty.");
        }

        var parts = basePart.Split('/');
        if (parts.Length < 2 || !string.Equals(parts[0], Theory, StringComparison.Ordinal))
        {
            throw new FormatException("Only the instantiated D5 coordinate is admissible.");
        }

        var plane = parts[1] switch
        {
            "B" => Plane.Blueprint,
            "E" => Plane.Evidence,
            "C" => Plane.Chronicle,
            "L" => Plane.Library,
            "P" => Plane.Papers,
            _ => Plane.Formal,
        };
        var rest = plane is Plane.Formal ? parts[1..] : parts[2..];

        return plane switch
        {
            Plane.Formal => ParseFormal(rest, tag),
            Plane.Blueprint => ParseBlueprint(rest, tag),
            Plane.Evidence => ParseEvidence(rest, tag),
            Plane.Chronicle => ParseChronicle(rest, tag),
            Plane.Library => ParseLibrary(rest, tag),
            Plane.Papers => ParsePaper(rest, tag),
            _ => throw new InvalidOperationException("Unknown plane value."),
        };
    }

    private static Target ParseFormal(string[] rest, string? tag)
    {
        if (tag is not null)
        {
            throw new FormatException("Formal GID cannot carry a tag.");
        }

        var (coordinates, module, declaration) = ParseFormalCoordinates(rest);
        var path = RepoPath.CreateKnown(
            string.Join('/', new[] { Theory }.Concat(coordinates.Values[..^1]))
            + $"/{module}.lean");
        return new Target.Formal(Theory, coordinates, path, declaration);
    }

    private static Target ParseBlueprint(string[] rest, string? tag)
    {
        if (tag is not null)
        {
            throw new FormatException("Blueprint GID cannot carry a tag.");
        }

        var (coordinates, module, declaration) = ParseFormalCoordinates(rest);
        if (declaration is not null)
        {
            throw new FormatException("Blueprint target cannot select a declaration.");
        }

        var path = RepoPath.CreateKnown(
            string.Join('/', new[] { "Blueprint", Theory }.Concat(coordinates.Values[..^1]))
            + $"/{module}.md");
        return new Target.Blueprint(Theory, coordinates, path);
    }

    private static Target ParseEvidence(string[] rest, string? tag)
    {
        if (!ArtifactKindId.TryCreate(tag, out var artifactKind) || rest.Length == 0)
        {
            throw new FormatException("Evidence GID requires an artifact kind.");
        }

        var pieces = rest[^1].Split('.');
        if (pieces.Length != 2 || !IsSafeSegment(pieces[0]) || !IsSafeSegment(pieces[1]))
        {
            throw new FormatException("Evidence GID requires exactly one selector.");
        }

        var module = pieces[0];
        var selector = pieces[1];
        CoordinatePath coordinates;
        if (rest.Length == 1 && string.Equals(module, "values", StringComparison.Ordinal))
        {
            coordinates = CoordinatePath.Create(new[] { module });
        }
        else if (rest.Length == 2 && string.Equals(rest[0], "experiments", StringComparison.Ordinal))
        {
            if (!ExperimentPattern.IsMatch(module))
            {
                throw new FormatException("Experiment module is not canonical.");
            }

            coordinates = CoordinatePath.Create(new[] { rest[0], module });
        }
        else if (rest.Length == 2 && string.Equals(rest[0], "kernels", StringComparison.Ordinal))
        {
            if (!CamelPattern.IsMatch(module))
            {
                throw new FormatException("Kernel module is not canonical.");
            }

            coordinates = CoordinatePath.Create(new[] { rest[0], module });
        }
        else
        {
            var formal = rest[..^1].Append(module).ToArray();
            var parsed = ParseFormalCoordinates(formal);
            if (parsed.Declaration is not null)
            {
                throw new FormatException("Evidence coordinates cannot select a declaration.");
            }

            coordinates = parsed.Coordinates;
        }

        var fileName = $"{module}.{selector}.{artifactKind.Value}";
        var path = RepoPath.CreateKnown(
            string.Join('/', new[] { "Evidence", Theory }.Concat(coordinates.Values[..^1]))
            + $"/{fileName}");
        return new Target.Evidence(Theory, coordinates, path, selector, artifactKind);
    }

    private static Target ParseChronicle(string[] rest, string? tag)
    {
        if (tag is not null
            || rest.Length != 2
            || !DatePattern.IsMatch(rest[0])
            || !IsSafeSegment(rest[1]))
        {
            throw new FormatException("Chronicle GID is not canonical.");
        }

        var dateParts = rest[0].Split('-');
        var path = RepoPath.CreateKnown(
            $"Chronicle/{dateParts[0]}/{dateParts[1]}/{dateParts[2]}-{rest[1]}.md");
        return new Target.Chronicle(Theory, CoordinatePath.Create(rest), path);
    }

    private static Target ParseLibrary(string[] rest, string? tag)
    {
        if (tag is not null || rest.Length != 1 || !IsSafeSegment(rest[0]))
        {
            throw new FormatException("Library GID is not canonical.");
        }

        var path = RepoPath.CreateKnown($"Library/notes/{rest[0]}.md");
        return new Target.Library(Theory, CoordinatePath.Create(rest), path);
    }

    private static Target ParsePaper(string[] rest, string? tag)
    {
        if (rest.Length != 1 || !PaperPattern.IsMatch(rest[0]) || tag is not null and not "frozen")
        {
            throw new FormatException("Paper GID is not canonical.");
        }

        var frozen = tag is not null;
        var path = RepoPath.CreateKnown(
            frozen
                ? $"Papers/frozen/{rest[0]}/manifest.sha256"
                : $"Papers/recipes/{rest[0]}.yaml");
        return new Target.Paper(Theory, CoordinatePath.Create(rest), path, frozen);
    }

    private static (CoordinatePath Coordinates, string Module, string? Declaration)
        ParseFormalCoordinates(string[] parts)
    {
        var ordinary = parts.Length == 3
            && IsStratum(parts[0])
            && CamelPattern.IsMatch(parts[1]);
        var special = parts.Length == 2 && IsSpecialZone(parts[0]);
        if (!ordinary && !special)
        {
            throw new FormatException("Formal coordinates are not canonical.");
        }

        var final = parts[^1].Split('.');
        if (final.Length is < 1 or > 2 || !CamelPattern.IsMatch(final[0]))
        {
            throw new FormatException("Formal module is not canonical.");
        }

        var declaration = final.Length == 2 ? final[1] : null;
        if (declaration is not null && !DeclarationPattern.IsMatch(declaration))
        {
            throw new FormatException("Declaration selector is not canonical.");
        }

        var coordinates = parts[..^1].Append(final[0]);
        return (CoordinatePath.Create(coordinates), final[0], declaration);
    }

    private static string Print(Target target) => target switch
    {
        Target.Formal formal =>
            $"{formal.Theory}/{string.Join('/', formal.Coordinates.Values)}"
            + (formal.Declaration is null ? string.Empty : $".{formal.Declaration}"),
        Target.Blueprint blueprint =>
            $"{blueprint.Theory}/B/{string.Join('/', blueprint.Coordinates.Values)}",
        Target.Evidence evidence =>
            $"{evidence.Theory}/E/{string.Join('/', evidence.Coordinates.Values)}"
            + $".{evidence.Selector}{TagSeparator}{evidence.ArtifactKind.Value}",
        Target.Chronicle chronicle =>
            $"{chronicle.Theory}/C/{string.Join('/', chronicle.Coordinates.Values)}",
        Target.Library library =>
            $"{library.Theory}/L/{string.Join('/', library.Coordinates.Values)}",
        Target.Paper paper =>
            $"{paper.Theory}/P/{string.Join('/', paper.Coordinates.Values)}"
            + (paper.Frozen ? $"{TagSeparator}frozen" : string.Empty),
    };

    private static bool IsStratum(string value) => value is "S0" or "S1" or "S2" or "S3" or "S4";

    private static bool IsSpecialZone(string value) =>
        value is "X_Assumptions" or "X_Certificates" or "X_Frontier";

    private static bool IsSafeSegment(string value) =>
        value is not "." and not ".." && SafeSegmentPattern.IsMatch(value);
}
