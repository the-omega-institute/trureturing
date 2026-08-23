using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal void ReviseTheoristStatementWithoutRevision()
    {
        var declaration = Assert.Single(Reports[currentTheoristPath].Declarations);
        var revised = declaration with
        {
            TypeRepresentation = "statement-v2(revised-frontier-contract)",
        };
        Reports[currentTheoristPath] = Report(declarations: [revised]);
        RewriteCurrentContract(root =>
        {
            root["exact_statement"]!.AsObject()["statement_sha256"] =
                CanonicalStatementWriter.StatementTypeAddress(revised.TypeRepresentation);
            root.Remove("revision");
        });
    }

    internal void ReviseTheoristStatementWithRevision(
        string kind,
        string? predecessorSha256 = null,
        string? caseId = null,
        string note = "fixture revision declaration")
    {
        var baselineDeclaration = Assert.Single(BaselineReports[currentTheoristPath].Declarations);
        predecessorSha256 ??=
            CanonicalStatementWriter.StatementTypeAddress(baselineDeclaration.TypeRepresentation);
        ReviseTheoristStatementWithoutRevision();
        RewriteCurrentContract(root =>
        {
            var revision = new JsonObject
            {
                ["predecessor_sha256"] = predecessorSha256,
                ["kind"] = kind,
                ["note"] = note,
            };
            if (caseId is not null)
            {
                revision["case_id"] = caseId;
            }

            root["revision"] = revision;
        });
    }

    internal void AddUnexpectedRevisionField() =>
        RewriteCurrentContract(root =>
            root["revision"]!.AsObject()["unexpected"] = true);

    internal void AddRevisionToRetiredBaseline(
        string kind,
        string? caseId = null,
        string note = "historical fixture revision")
    {
        RewriteBaselineContract(root =>
        {
            var revision = new JsonObject
            {
                ["predecessor_sha256"] =
                    "sha256:0000000000000000000000000000000000000000000000000000000000000000",
                ["kind"] = kind,
                ["note"] = note,
            };
            if (caseId is not null)
            {
                revision["case_id"] = caseId;
            }

            root["revision"] = revision;
        });
    }

    private void RewriteCurrentContract(Action<JsonObject> rewrite)
    {
        var source = Files[currentTheoristPath];
        Files[currentTheoristPath] = RewriteContract(source, rewrite);
    }

    private void RewriteBaselineContract(Action<JsonObject> rewrite)
    {
        var source = Baseline[currentTheoristPath];
        Baseline[currentTheoristPath] = RewriteContract(source, rewrite);
    }

    private static string RewriteContract(string source, Action<JsonObject> rewrite)
    {
        var start = source.IndexOf(
            TheoristFrontierContractValidator.Marker,
            StringComparison.Ordinal);
        Assert.True(start >= 0);
        start += TheoristFrontierContractValidator.Marker.Length;
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(end > start);
        var root = JsonNode.Parse(source[start..end])!.AsObject();
        rewrite(root);
        return source[..start]
            + root.ToJsonString()
            + source[end..];
    }
}
