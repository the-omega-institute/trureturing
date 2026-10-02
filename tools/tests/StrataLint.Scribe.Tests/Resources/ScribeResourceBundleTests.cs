using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceBundleTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReaderRejectsTruncatedResourceOrOutOfRangeLength(bool oversizedLength)
    {
        var bytes = Carrier(ScribeReleaseSurface.ResourceName);
        using var pe = new PEReader(new MemoryStream(bytes));
        var directory = pe.PEHeaders.CorHeader!.ResourcesDirectory;
        var section = pe.PEHeaders.SectionHeaders.Single(item => directory.RelativeVirtualAddress >= item.VirtualAddress
            && directory.RelativeVirtualAddress < item.VirtualAddress + item.VirtualSize);
        var offset = section.PointerToRawData + directory.RelativeVirtualAddress - section.VirtualAddress;
        if (oversizedLength)
            System.Buffers.Binary.BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(offset, sizeof(int)), int.MaxValue);
        else
            bytes = bytes[..(offset + sizeof(int) + 1)];
        var exception = Assert.ThrowsAny<FormatException>(() => ScribeReleaseSurface.Unbundle(bytes));
        Assert.StartsWith(oversizedLength ? "InvalidResource:" : "InvalidAssembly:", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("InvalidAssembly")]
    [InlineData("MissingResource")]
    [InlineData("MultipleResources")]
    [InlineData("ResourceNameMismatch")]
    public void ReaderRejectsInvalidCarrierWithNamedReason(string reason)
    {
        var bytes = reason switch
        {
            "InvalidAssembly" => new byte[] { 0xff },
            "MissingResource" => Carrier(),
            "MultipleResources" => Carrier(ScribeReleaseSurface.ResourceName, "additional"),
            _ => Carrier("other"),
        };
        var exception = Assert.ThrowsAny<FormatException>(() => ScribeReleaseSurface.Unbundle(bytes));
        Assert.StartsWith(reason + ":", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WriterRoundTripsPackBytesDeterministicallyWithOnlyModuleType()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("pack.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First")]);
        var packBytes = File.ReadAllBytes(path);
        var first = ScribeReleaseSurface.Bundle(packBytes);
        Assert.Equal(first, ScribeReleaseSurface.Bundle(packBytes));
        Assert.Equal(packBytes, ScribeReleaseSurface.Unbundle(first));
        Assert.Single(ScribeReleaseSurface.OpenBundle(first).ReadAll());
        using var pe = new PEReader(new MemoryStream(first));
        var metadata = pe.GetMetadataReader();
        var type = Assert.Single(metadata.TypeDefinitions);
        Assert.Equal("<Module>", metadata.GetString(metadata.GetTypeDefinition(type).Name));
        var resource = metadata.GetManifestResource(Assert.Single(metadata.ManifestResources));
        Assert.True(resource.Implementation.IsNil);
        Assert.Equal(ScribeReleaseSurface.ResourceName, metadata.GetString(resource.Name));
    }

    [Fact]
    public void ReaderExtractsResourceWithoutLoadingCarrier()
    {
        var bytes = Carrier(ScribeReleaseSurface.ResourceName);
        Assert.DoesNotContain(AppDomain.CurrentDomain.GetAssemblies(),
            assembly => assembly.GetName().Name == "NeutralResourceCarrier");
        Assert.Equal(new byte[] { 1, 2, 3 }, ScribeReleaseSurface.Unbundle(bytes));
        Assert.DoesNotContain(AppDomain.CurrentDomain.GetAssemblies(),
            assembly => assembly.GetName().Name == "NeutralResourceCarrier");
    }

    internal static byte[] Carrier(params string[] names)
    {
        var compilation = CSharpCompilation.Create("NeutralResourceCarrier", references:
            [MetadataReference.CreateFromFile(typeof(object).Assembly.Location)], options:
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, deterministic: true));
        using var stream = new MemoryStream();
        var emitted = compilation.Emit(stream, manifestResources: names.Select(name =>
            new ResourceDescription(name, () => new MemoryStream([1, 2, 3], writable: false), isPublic: true)));
        Assert.True(emitted.Success, string.Join(Environment.NewLine, emitted.Diagnostics));
        return stream.ToArray();
    }
}
