using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace StrataLint.Scribe;

public enum ScribeResourceBundleErrorCode
{
    EmitFailed, InvalidAssembly, MissingResource, MultipleResources, ResourceNameMismatch, InvalidResource,
}

public sealed class ScribeResourceBundleException : FormatException
{
    public ScribeResourceBundleException(ScribeResourceBundleErrorCode reasonCode, string message, Exception? inner = null)
        : base($"{reasonCode}: {message}", inner) => ReasonCode = reasonCode;

    public ScribeResourceBundleErrorCode ReasonCode { get; }
}

/// <summary>A metadata-only carrier for one resource pack; reading never loads its assembly.</summary>
public static class ScribeResourceBundle
{
    public const string FileName = "StrataLint.Scribe.ResourceBundle.dll";
    public const string ResourceName = "scribe-resources.zip";

    public static byte[] Write(byte[] packBytes)
    {
        ArgumentNullException.ThrowIfNull(packBytes);
        var compilation = CSharpCompilation.Create("StrataLint.Scribe.ResourceBundle",
            references: [MetadataReference.CreateFromFile(typeof(object).Assembly.Location)],
            options: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary,
                optimizationLevel: OptimizationLevel.Release, deterministic: true));
        using var output = new MemoryStream();
        var result = compilation.Emit(output, manifestResources:
            [new ResourceDescription(ResourceName, () => new MemoryStream(packBytes, writable: false), isPublic: true)]);
        if (!result.Success)
            throw Error(ScribeResourceBundleErrorCode.EmitFailed, string.Join(Environment.NewLine, result.Diagnostics));
        return output.ToArray();
    }

    public static ScribeResourcePack Open(string path)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        return Open(File.ReadAllBytes(path));
    }

    public static ScribeResourcePack Open(byte[] assemblyBytes) => ScribeResourcePack.Open(ReadPackBytes(assemblyBytes));

    public static byte[] ReadPackBytes(byte[] assemblyBytes)
    {
        ArgumentNullException.ThrowIfNull(assemblyBytes);
        try
        {
            using var stream = new MemoryStream(assemblyBytes, writable: false);
            using var pe = new PEReader(stream);
            if (!pe.HasMetadata || pe.PEHeaders.CorHeader is not { } header)
                throw Error(ScribeResourceBundleErrorCode.InvalidAssembly, "The carrier is not a managed PE assembly.");
            var metadata = pe.GetMetadataReader();
            if (metadata.ManifestResources.Count == 0)
                throw Error(ScribeResourceBundleErrorCode.MissingResource, "The carrier has no embedded resource.");
            if (metadata.ManifestResources.Count != 1)
                throw Error(ScribeResourceBundleErrorCode.MultipleResources, "The carrier must have exactly one resource.");
            var resource = metadata.GetManifestResource(metadata.ManifestResources.Single());
            if (metadata.GetString(resource.Name) != ResourceName)
                throw Error(ScribeResourceBundleErrorCode.ResourceNameMismatch, $"The resource must be named {ResourceName}.");
            var directory = header.ResourcesDirectory;
            if (!resource.Implementation.IsNil || directory.Size < sizeof(int)
                || resource.Offset > (long)directory.Size - sizeof(int))
                throw Error(ScribeResourceBundleErrorCode.InvalidResource, "The resource is not embedded in the carrier.");
            var block = pe.GetSectionData(directory.RelativeVirtualAddress);
            if (directory.Size > block.Length)
                throw Error(ScribeResourceBundleErrorCode.InvalidResource, "The resource directory exceeds the PE section.");
            var reader = block.GetReader((int)resource.Offset, directory.Size - (int)resource.Offset);
            var length = reader.ReadInt32();
            if (length < 0 || length > reader.RemainingBytes)
                throw Error(ScribeResourceBundleErrorCode.InvalidResource, "The embedded resource length is invalid.");
            return reader.ReadBytes(length);
        }
        catch (Exception exception) when (exception is BadImageFormatException or IOException or ArgumentOutOfRangeException)
        {
            throw new ScribeResourceBundleException(ScribeResourceBundleErrorCode.InvalidAssembly,
                "The carrier is not a readable PE assembly.", exception);
        }
    }

    private static ScribeResourceBundleException Error(ScribeResourceBundleErrorCode reason, string message) => new(reason, message);
}
