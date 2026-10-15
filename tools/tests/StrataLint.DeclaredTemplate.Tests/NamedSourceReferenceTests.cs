using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class NamedSourceReferenceTests
{
    [Theory]
    [InlineData(false, "valid")]
    [InlineData(true, "valid")]
    [InlineData(true, "permuted-universes")]
    [InlineData(true, "instantiated-universe")]
    [InlineData(true, "metadata-wrapper")]
    [InlineData(true, "missing-material")]
    [InlineData(true, "wrong-polarity")]
    [InlineData(false, "wrong-name")]
    [InlineData(false, "wrong-reference")]
    [InlineData(true, "wrong-statement")]
    [InlineData(false, "wrong-level-count")]
    [InlineData(false, "duplicate-universes")]
    [InlineData(false, "definition-not-prop")]
    [InlineData(false, "malformed-name")]
    [InlineData(false, "trailing-material")]
    [InlineData(false, "legacy-identity")]
    [InlineData(true, "legacy-identity")]
    public void named_reference_uses_raw_rigid_universes_and_structural_names(bool negated, string mutation)
    {
        // Synthetic statement-v1 materials exercise the bounded grammar beyond
        // the native clients' zero universes: UTF-8, quoted dots and a num node.
        const string nameKey = "ns(nn(ns(ns(ns(n0,2:D5),5:Probe),4:x.λ),7),5:claim)";
        const string referenceHash = "c2a7b544a37d5ebffb374626811f1f05e53ee417c7c877f4eddb4d56c7342b32";
        const string negativeHash = "55a8a220458148df16faf815f13d4ca0c7e2637159d82d836c2b8bd4b9262f10";
        const string parameters = "ns(n0,1:u),ns(n0,1:v)";
        var levels = mutation switch {
            "permuted-universes" => "lp(ns(n0,1:v)),lp(ns(n0,1:u))",
            "instantiated-universe" => "l0,lp(ns(n0,1:v))",
            _ => "lp(ns(n0,1:u)),lp(ns(n0,1:v))",
        };
        var rawReference = "ec(" + nameKey + ",[" + levels + "])";
        var rawType = negated && mutation != "wrong-polarity"
            ? "ea(ec(ns(n0,3:Not),[])," + rawReference + ")" : rawReference;
        if (mutation == "metadata-wrapper") rawType = "ed(" + rawType + ")";
        var theorem = new LeanDeclaration("D5.Probe.result", "theorem",
            mutation == "missing-material" ? "unavailable"
                : "statement-v1(uparams=[" + (mutation == "duplicate-universes"
                    ? "ns(n0,1:u),ns(n0,1:u)" : parameters) + "],type=" + rawType + ")"
                    + (mutation == "trailing-material" ? "x" : ""), []);
        var definition = new LeanDeclaration("D5.Probe.«x.λ».7.claim", "def",
            "statement-v1(uparams=[ns(n0,1:a),ns(n0,1:b)],type="
                + (mutation == "definition-not-prop" ? "es(ls(l0))" : "es(l0)") + ",value=fixture)", []) {
            NameKey = mutation == "wrong-name" ? nameKey.Replace("5:claim", "5:other", StringComparison.Ordinal)
                : mutation == "malformed-name" ? nameKey + "x" : nameKey };
        var binding = JsonSerializer.SerializeToElement(new {
            level_count = mutation == "wrong-level-count" ? 1 : 2,
            definition_entry = new { path = negated ? new[] { "arg" } : Array.Empty<string>(),
                reference_identity = mutation == "wrong-reference" ? new string('0', 64)
                    : mutation == "legacy-identity" ? "65960cfc15c52484d5f0825d7c9279debbdd37c841d4c3eddb3f9461b8cf9df9"
                    : referenceHash },
        });
        void Check() => InformationTemplateDefinitionReference.Check(binding,
            mutation == "wrong-statement" ? new string('0', 64)
                : mutation == "legacy-identity"
                    ? negated ? "707564a4041c1bf2627e069ead2754a3de3c4bfc60642f419a2e2ec671a61f91"
                        : "65960cfc15c52484d5f0825d7c9279debbdd37c841d4c3eddb3f9461b8cf9df9"
                    : negated ? negativeHash : referenceHash, theorem, definition);
        if (mutation == "valid") Check();
        else Assert.Throws<FormatException>(Check);
    }

    // Hashes are checked against compactRawIdentity by NamedReferenceIdentity.lean.
    public static IEnumerable<object[]> ProducerVectors()
    {
        yield return new object[] { "rich", "c2a7b544a37d5ebffb374626811f1f05e53ee417c7c877f4eddb4d56c7342b32", "55a8a220458148df16faf815f13d4ca0c7e2637159d82d836c2b8bd4b9262f10" };
        yield return new object[] { "plain", "febd552b62dbe8d57db873ee5a4a4d7bcc0dc35108a6c84706eecd5b20ca580f", "adc05d5f0f79aa2d665056f434d4e18294317c4cb8fa8e52e7bf43a12593ee3d" };
        yield return new object[] { "shared", "d6cf4aab8d84077ad0c3ff1c58335426114f38938757d85854325b5221bff502", "590ceb3960601fb9bfa40855bbd1debf753bd2d80d7c54d1fe5e82f65506d14c" };
        yield return new object[] { "numericShared", "87f795426861d7c2b8e99a8777b1168e2b1864cb3e47eb42382ecf16e2f4f936", "648d31ccb57d7c1f05169f687a10cb94c0c1bbf0857b9023b44ef3b513e1765e" };
        yield return new object[] { "empty", "266610d3f5d1e520f637b1df809212f868c034ffc6ffedd13710dfc1b268f0d1", "a1b15196e2e2d686400229fbcb4bf88daa93bc6bcf2403b21c131ab6afb1e522" };
        yield return new object[] { "tokens", "e4f88bd090ff59f4345ce7a0f7a90b15aa05295462b1cbfd04b2e80ee1b7e7c3", "f11b68359b452f9bade3e426cdedd147f1ad9e99027222dbd19d46fc06b2f13b" };
        yield return new object[] { "depth", "16297bbbfa56d2f98ec0a92d30a7476570e8adbdc546adcb87bc6f2bf2429eeb", "3182e3f77cc339c34a98e119c4386a3c1894677f7897b050dfc82b70689e6bba" };
        yield return new object[] { "universes", "e5178923f96a6704f99a6a766f7e7ff230c29e0e42da405172ee5755954fa4fe", "3eec8cdc8605b872aff57a322cb3b96db8e11b2526b49d91fe5decfb9c5b83b7" };
    }

    [Theory]
    [MemberData(nameof(ProducerVectors))]
    public void current_producer_vectors_accept_both_entry_forms(string label, string referenceHash, string negativeHash)
    {
        var nameKey = label switch {
            "rich" => "ns(nn(ns(ns(ns(n0,2:D5),5:Probe),4:x.λ),7),5:claim)",
            "shared" => "ns(ns(n0,3:Not),5:claim)",
            "numericShared" => "ns(nn(ns(n0,3:Not),7),5:claim)",
            "empty" => "ns(ns(n0,7:Fixture),0:)",
            "tokens" => "ns(ns(ns(n0,9:expr-node),5:const),8:name-ref)",
            "depth" => Enumerable.Range(0, 256).Aggregate("n0", (parent, _) => "ns(" + parent + ",1:x)"),
            _ => "ns(ns(n0,7:Fixture),5:claim)",
        };
        var parameters = label == "rich" ? new[] { "ns(n0,1:u)", "ns(n0,1:v)" }
            : label == "universes" ? Enumerable.Range(0, 64).Select(i => "nn(ns(n0,1:u)," + i + ")").ToArray()
            : Array.Empty<string>();
        var rawReference = "ec(" + nameKey + ",[" + string.Join(",", parameters.Select(p => "lp(" + p + ")")) + "])";
        var definition = new LeanDeclaration("Fixture.claim", "def",
            "statement-v1(uparams=[" + string.Join(",", parameters) + "],type=es(l0),value=fixture)", []) { NameKey = nameKey };
        foreach (var negated in new[] { false, true })
        {
            var theorem = new LeanDeclaration("Fixture.result", "theorem",
                "statement-v1(uparams=[" + string.Join(",", parameters) + "],type="
                    + (negated ? "ea(ec(ns(n0,3:Not),[])," + rawReference + ")" : rawReference) + ")", []);
            var binding = JsonSerializer.SerializeToElement(new { level_count = parameters.Length,
                definition_entry = new { path = negated ? new[] { "arg" } : Array.Empty<string>(), reference_identity = referenceHash } });
            InformationTemplateDefinitionReference.Check(binding, negated ? negativeHash : referenceHash, theorem, definition);
        }
    }

    [Theory]
    [InlineData("universes", "source definition universe bound")]
    [InlineData("name", "Name depth exceeds source bound")]
    public void raw_input_bounds_remain_enforced(string mutation, string diagnostic)
    {
        var nameKey = mutation == "name"
            ? Enumerable.Range(0, 257).Aggregate("n0", (parent, _) => "ns(" + parent + ",1:x)")
            : "ns(ns(n0,7:Fixture),5:claim)";
        var parameters = mutation == "universes"
            ? Enumerable.Range(0, 65).Select(i => "nn(ns(n0,1:u)," + i + ")").ToArray() : [];
        var theorem = new LeanDeclaration("Fixture.result", "theorem",
            "statement-v1(uparams=[" + string.Join(",", parameters) + "],type=ec(" + nameKey + ",[]))", []);
        var definition = new LeanDeclaration("Fixture.claim", "def",
            "statement-v1(uparams=[],type=es(l0),value=fixture)", []) { NameKey = nameKey };
        var binding = JsonSerializer.SerializeToElement(new { level_count = parameters.Length,
            definition_entry = new { path = Array.Empty<string>(), reference_identity = new string('0', 64) } });
        var error = Assert.Throws<FormatException>(() => InformationTemplateDefinitionReference.Check(
            binding, new string('0', 64), theorem, definition));
        Assert.Contains(diagnostic, error.Message, StringComparison.Ordinal);
    }
}
