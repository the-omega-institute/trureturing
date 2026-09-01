using System.Collections.Immutable;
using System.Reflection;
using System.Runtime.CompilerServices;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public interface IScribeDocumentDefinition
{
    DocumentDefinition Create();
}

public sealed record DocumentDefinition
{
    private DocumentDefinition(ScribeDocument document, string sourcePath)
    {
        Document = document;
        SourcePath = sourcePath;
    }

    public ScribeDocument Document { get; }

    public RepoPath RelativePath => Document.Header.MirrorBlueprint.Path;

    public string SourcePath { get; }

    public static DocumentDefinition Create(
        ScribeDocument document,
        [CallerFilePath] string sourcePath = "")
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourcePath);
        return new DocumentDefinition(document, sourcePath);
    }

    internal DocumentDefinition ResolveDeclarations(DeclarationCatalog catalog) =>
        new(Document.ResolveDeclarations(catalog), SourcePath);
}

public static class DocumentDefinitions
{
    private static readonly Lazy<ImmutableArray<DocumentDefinition>> Definitions = new(
        () => Discover(typeof(DocumentDefinitions).Assembly));

    [CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
    public static ImmutableArray<DocumentDefinition> All => Definitions.Value;

    public static ImmutableArray<DocumentDefinition> Discover(Assembly assembly)
    {
        ArgumentNullException.ThrowIfNull(assembly);
        return DiscoverCore(assembly);
    }

    public static ImmutableArray<DocumentDefinition> Discover(
        Assembly assembly,
        string repositoryRoot)
    {
        ArgumentNullException.ThrowIfNull(assembly);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);

        return StatementProjectionFixtureLoader.WithRepositoryRoot(
            repositoryRoot,
            () => DiscoverCore(assembly));
    }

    internal static string[] CheckRepositorySourceBijection(
        IEnumerable<string> filesystemSources,
        IEnumerable<DocumentDefinition> definitions)
    {
        ArgumentNullException.ThrowIfNull(filesystemSources);
        ArgumentNullException.ThrowIfNull(definitions);
        var actual = filesystemSources
            .Select(static path => path.Replace('\\', '/'))
            .ToHashSet(StringComparer.Ordinal);
        var registered = definitions
            .Select(static definition => ScribeEmissionAttestation.DefinitionPath(
                definition.Document.Header.Gid.Value))
            .ToHashSet(StringComparer.Ordinal);
        return actual
            .Except(registered, StringComparer.Ordinal)
            .Select(static path => $"unregistered Scribe source: {path}")
            .Concat(registered
                .Except(actual, StringComparer.Ordinal)
                .Select(static path => $"registered Scribe source is missing: {path}"))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static ImmutableArray<DocumentDefinition> DiscoverCore(Assembly assembly)
    {
        var definitions = assembly.GetTypes()
            .Where(static type =>
                !type.IsAbstract
                && typeof(IScribeDocumentDefinition).IsAssignableFrom(type))
            .OrderBy(static type => type.FullName, StringComparer.Ordinal)
            .Select(CreateDefinition)
            .OrderBy(static definition => definition.RelativePath.Value, StringComparer.Ordinal)
            .ToImmutableArray();

        var duplicate = definitions
            .GroupBy(static definition => definition.RelativePath.Value, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1);
        if (duplicate is not null)
        {
            throw new InvalidOperationException(
                $"Multiple Scribe definitions target {duplicate.Key}.");
        }

        return definitions;
    }

    private static DocumentDefinition CreateDefinition(Type type)
    {
        var instance = Activator.CreateInstance(type, nonPublic: true)
            as IScribeDocumentDefinition
            ?? throw new InvalidOperationException(
                $"Scribe definition {type.FullName} needs a parameterless constructor.");
        var definition = instance.Create()
            ?? throw new InvalidOperationException(
                $"Scribe definition {type.FullName} returned null.");
        ValidateBijection(definition);
        return definition;
    }

    private static void ValidateBijection(DocumentDefinition definition)
    {
        var gid = definition.Document.Header.Gid.Value;
        var expected = "Blueprint/D5/" + gid["D5/".Length..] + ".scribe.cs";
        var actual = definition.SourcePath.Replace('\\', '/');
        if (!string.Equals(actual, expected, StringComparison.Ordinal)
            && !actual.EndsWith('/' + expected, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"Scribe definition {gid} must be declared in {expected}, not {actual}.");
        }
    }
}
