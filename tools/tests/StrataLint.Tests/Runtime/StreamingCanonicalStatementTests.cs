using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class StreamingCanonicalStatementTests
{
    public static TheoryData<string> Materials => new()
    {
        "",
        "statement-v1(test)",
        "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))",
        "statement-v1(uparams=[],type=ec(ns(n0,6:String),[]),value=ei(lt(4:𝒪)))",
        "∀ α, Ω𝒪😀\"\\\b\f\n\r\t\0\u001f<>&+' /\u007f\u0085\u00a0\u2028\u2029\ufeff",
        "\ufeff\U00010000\U0001fffe\U0001ffff\U000e0001\U0010fffe\U0010ffff",
        new string(Enumerable.Range(0, 65536).Select(value => (char)value).ToArray()),
        "before\ud800after\udc00last\ud800",
        new string('a', 16383) + "𝒪😀\n" + new string('b', 16383) + "\ud800",
    };

    [Theory]
    [MemberData(nameof(Materials))]
    public void StreamingPreimageAndAddressMatchTheEstablishedCanonicalWriter(string material)
    {
        var path = RepoPath.CreateKnown("D5/S3/VertexAlgebra/Probe.lean");
        var declaration = new LeanDeclaration("probe𝒪", "def", material, [])
        {
            NameKey = "ns(n0,9:probe𝒪)",
        };
        var legacy = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            declaration_name_key = declaration.NameKey,
            kind = declaration.Kind,
            module_path = path.Value,
            schema = "declaration-statement-v1",
            statement_material = material,
        }));
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        hash.AppendData("trureturing:statement:v1\0"u8);
        hash.AppendData(legacy.AsSpan());
        var expectedAddress = "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset());
        foreach (var fragmentSize in new[] { 1, 2, 7, 16384 })
        {
            using var destination = new MemoryStream();
            using var reader = new FragmentedReader(material, fragmentSize);
            CanonicalStatementWriter.WriteDeclaration(destination, path, declaration, reader);
            Assert.Equal(legacy.ToArray(), destination.ToArray());
            using var addressReader = new FragmentedReader(material, fragmentSize);
            Assert.Equal(expectedAddress,
                CanonicalStatementWriter.DeclarationStatementId(path, declaration, addressReader));
        }
        if (material.Length > 0)
            Assert.Equal(expectedAddress, CanonicalStatementWriter.DeclarationStatementId(path, declaration));
    }

    [Fact]
    public void CanonicalBytesRetainSpacingNewlineAndSupplementaryEscapes()
    {
        var declaration = new LeanDeclaration("probe", "axiom", "𝒪😀\n\"\\", []);
        using var destination = new MemoryStream();
        using var reader = new StringReader(declaration.TypeRepresentation);
        CanonicalStatementWriter.WriteDeclaration(destination, RepoPath.CreateKnown("Trureturing.lean"), declaration, reader);
        Assert.Equal(
            "{\"declaration_name_key\": \"probe\", \"kind\": \"axiom\", \"module_path\": \"Trureturing.lean\", "
            + "\"schema\": \"declaration-statement-v1\", \"statement_material\": \"\\uD835\\uDCAA\\uD83D\\uDE00\\n\\\"\\\\\"}\n",
            Encoding.UTF8.GetString(destination.ToArray()));
    }

    private sealed class FragmentedReader(string material, int fragmentSize) : StringReader(material)
    {
        public override int Read(Span<char> buffer) => base.Read(buffer[..Math.Min(buffer.Length, fragmentSize)]);
    }
}
