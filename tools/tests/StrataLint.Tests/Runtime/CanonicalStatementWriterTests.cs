using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CanonicalStatementWriterTests
{
    [Theory]
    [InlineData("statement-v1(test)")]
    [InlineData("中文 αβ e\u0301 😀\n\r\t\b\f\"\\ / <>&+\u2028\uFFFF")]
    public void DeclarationIdentityMatchesTheOriginalCanonicalBytesAndDomain(string material)
    {
        var path = RepoPath.CreateKnown("Trureturing.lean");
        var declaration = new LeanDeclaration("probe", "axiom", material, [])
        {
            NameKey = "ns(n0,5:probe)",
        };
        var element = JsonSerializer.SerializeToElement(new
        {
            declaration_name_key = declaration.NameKey,
            kind = declaration.Kind,
            module_path = path.Value,
            schema = "declaration-statement-v1",
            statement_material = material,
        });
        var options = new JsonSerializerOptions { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
        var expectedBytes = new UTF8Encoding(false, true).GetBytes("{" + string.Join(", ",
            element.EnumerateObject().OrderBy(static p => p.Name, StringComparer.Ordinal)
                .Select(p => JsonSerializer.Serialize(p.Name, options) + ": "
                    + JsonSerializer.Serialize(p.Value.GetString(), options))) + "}\n");

        Assert.Equal(FrozenContentHash.Compute(FrozenHashDomains.Statement, expectedBytes),
            CanonicalStatementWriter.DeclarationStatementId(path, declaration));
        if (material == "statement-v1(test)")
            Assert.Equal("sha256:452d97f1469d85ac204ab83dbbb919e19289c28674b14ab9df96586c535b1763",
                CanonicalStatementWriter.DeclarationStatementId(path, declaration));
    }
}
