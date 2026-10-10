using System.Text.Json;

namespace StrataLint.TestSupport;

internal static class InformationTemplateFixture
{
    internal static Dictionary<string, string> PolicyFiles() => new(StringComparer.Ordinal)
    {
        ["lean-toolchain"] = "leanprover/lean4:v4.33.0\n",
        ["lake-manifest.json"] = "{\"packages\":[]}",
        ["lean-report-inputs.json"] = """
            {"schema_version":1,"report_modules":{"include":[{"pattern":"D5/**/*.lean","optional":true},{"pattern":"Reg/**/*.lean","optional":true}],"exclude":[]},
             "inspector_sources":{"include":[],"exclude":[]},
             "dependency_sources":{"include":[],"exclude":[]},
             "config_inputs":{"include":[],"exclude":[]},"producer_scopes":{}}
            """,
    };

    internal static object FromSlot => new { name = "Bool", type_identity = new string('a', 64), object_identity = new string('b', 64) };
    internal static object OpenSlot => new { kind = "open", declaration_name = (string?)null,
        statement_identity = (string?)null, chain_name = (string?)null };

}
