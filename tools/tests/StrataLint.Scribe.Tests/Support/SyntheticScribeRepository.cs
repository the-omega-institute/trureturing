using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

/// <summary>
/// The smallest tree the emitter will accept: one document, its Scribe source, and the
/// digestion source metadata behind it. Tests judge this tree instead of the live one.
/// </summary>
internal static class SyntheticScribeRepository
{
    /// <summary>Writes the inputs <paramref name="definition"/> needs under a root.</summary>
    internal static void WriteInputs(string root, DocumentDefinition definition)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(root);
        ArgumentNullException.ThrowIfNull(definition);
        var definitionPath = Path.Combine(
            root,
            ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value));
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(definitionPath)!);
        TemporaryFileSystem.File.WriteAllText(
            definitionPath,
            "// synthetic Scribe source\n",
            new UTF8Encoding(false, true));

        var sourceMetadata = Path.Combine(
            root,
            "Meta", "Digestion", "backfill", "synthetic-source", "source.toml");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(sourceMetadata)!);
        TemporaryFileSystem.File.WriteAllText(
            sourceMetadata,
            """
            source_id = "synthetic-source"
            path = "docs/synthetic.md"
            atomizer = "synthetic-v1"
            genre_registry_check = "collected"
            unregistered_genres = []
            """ + "\n",
            new UTF8Encoding(false, true));
    }
}
