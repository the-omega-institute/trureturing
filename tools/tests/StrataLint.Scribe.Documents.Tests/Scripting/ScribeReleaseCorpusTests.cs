using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class ScribeReleaseCorpusTests(ITestOutputHelper output)
{
    [Fact]
    public void FullReleaseVerifiesAndBundleMatchesEveryAssemblyDefinition()
    {
        var root = FindRepositoryRoot();
        var temporary = Directory.CreateTempSubdirectory("scribe-release-corpus-");
        try
        {
            var target = Path.Combine(temporary.FullName, "release");
            var error = new StringWriter();
            Assert.Equal(0, ScribeCli.Run(typeof(DocumentAssembly).Assembly,
                ["resources", "release", "--out", target], root, TextWriter.Null, error));
            Assert.Empty(error.ToString());
            Assert.Equal(0, ScribeCli.Run(typeof(DocumentAssembly).Assembly,
                ["resources", "verify-release", "--dir", target], root, TextWriter.Null, error));
            Assert.Empty(error.ToString());
            Assert.Equal(new[] { "StrataLint.Scribe.ResourceBundle.dll", "scribe-resources.zip" },
                Directory.GetFiles(target).Select(Path.GetFileName).Order(StringComparer.Ordinal));
            var bytes = File.ReadAllBytes(Path.Combine(target, "StrataLint.Scribe.ResourceBundle.dll"));
            var type = typeof(ScribeResourcePack).Assembly.GetType("StrataLint.Scribe.ScribeResourceBundle");
            Assert.NotNull(type);
            var open = type.GetMethod("Open", [typeof(byte[])]);
            Assert.NotNull(open);
            var pack = Assert.IsType<ScribeResourcePack>(open.Invoke(null, [bytes]));
            Assert.Equal(DocumentAssembly.Definitions.Length, pack.Manifest.EntryCount);
            foreach (var definition in DocumentAssembly.Definitions)
            {
                Assert.Equal(ScribeResourceCodec.Encode(definition), ScribeResourceCodec.Encode(
                    pack.Read(definition.Document.Header.Gid.Value)));
            }
            using var pe = new PEReader(new MemoryStream(bytes));
            var metadata = pe.GetMetadataReader();
            var module = Assert.Single(metadata.TypeDefinitions);
            Assert.Equal("<Module>", metadata.GetString(metadata.GetTypeDefinition(module).Name));
            Assert.Single(metadata.ManifestResources);
            output.WriteLine($"release definitions={pack.Manifest.EntryCount}; mismatches=0; totalSha256={pack.Manifest.TotalSha256}; bundleTypeDefinitions={metadata.TypeDefinitions.Count}; zipBytes={new FileInfo(Path.Combine(target, "scribe-resources.zip")).Length}; bundleBytes={bytes.Length}");
        }
        finally { temporary.Delete(recursive: true); }
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Blueprint"))) return directory.FullName;
        }
        throw new DirectoryNotFoundException("repository root was not found");
    }
}
