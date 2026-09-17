using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.TestSupport;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateBindingRuleTests
{
    internal static RuleEvaluationContext Delta(bool declared = false, bool added = false,
        bool changed = true, bool invalid = false, bool missing = false, bool firstPin = false)
    {
        var before = Files();
        var after = new Dictionary<string, string>(before);
        if (changed) after[Registration] += "-- changed registration module\n";
        if (added) before.Remove(Registration);
        var report = Report(after, count: 1, declared: declared);
        if (invalid)
        {
            var wire = System.Text.Json.Nodes.JsonNode.Parse(RawLeanReportArtifact.Write(Tree(after), report).AsSpan())!;
            foreach (var module in wire["modules"]!.AsArray())
                foreach (var record in module!["information_templates"]!["records"]!.AsArray())
                {
                    record!["state"] = "declared_unresolved";
                    record["certificate"] = null;
                    record["diagnostic"] = "IE-C050 reason=invalid_template";
                }
            report = RawLeanReportArtifact.Read(
                Trureturing.Truth.StructuredCanonicalWriter.WriteJson(wire.ToJsonString()).AsSpan(), Tree(after));
        }
        if (missing) report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        var changes = new List<string> { Registration };
        if (firstPin)
        {
            const string pin = "Golden/Frozen/state/D5/S0/Carrier/Registration.lean.json";
            after[pin] = "{\"statement_id\":\"fixture\"}\n";
            changes = [pin];
        }
        return Context(before, after, report, changes.ToArray());
    }

    internal static void Finding(ImmutableArray<RuleFinding> findings, string name, AdmissionEffect effect)
    {
        Assert.True(findings.Length == 1 && findings[0].Message.StartsWith(name + " ", StringComparison.Ordinal)
            && (findings[0].Effect ?? AdmissionEffect.Block) == effect,
            "[FAIL] " + name + " expected=" + effect + ": " + string.Join("; ", findings.Select(f => f.Message)));
    }

    [Fact]
    public void unchanged_undeclared_registration_has_no_findings() =>
        Assert.Empty(DeclaredTemplateBindingRule.Evaluate(Delta(changed: false)));

    [Fact]
    public void unchanged_module_does_not_read_evidence() =>
        Assert.Empty(DeclaredTemplateBindingRule.Evaluate(Delta(changed: false, missing: true)));

    [Fact]
    public void changed_undeclared_registration_blocks() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta()), "DTR-Undeclared", AdmissionEffect.Block);

    [Fact]
    public void new_validated_registration_observes() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(declared: true, added: true)), "DTR-Declared", AdmissionEffect.Observe);

    [Fact]
    public void changed_unresolved_registration_blocks() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(declared: true, invalid: true)), "DTR-Evidence", AdmissionEffect.Block);

    [Fact]
    public void delta_missing_evidence_blocks() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(missing: true)), "DTR-Evidence", AdmissionEffect.Block);

    [Fact]
    public void first_pin_selects_registration() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(changed: false, firstPin: true)), "DTR-Undeclared", AdmissionEffect.Block);

    [Fact]
    public void deleted_finding_names_cannot_be_emitted()
    {
        var source = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Engine/Rules/TheoryGeneration/DeclaredTemplateBindingRule.cs"));
        var names = System.Text.RegularExpressions.Regex.Matches(source, "DTR-[A-Za-z]+")
            .Select(match => match.Value).Distinct().Order(StringComparer.Ordinal).ToArray();
        Assert.True(names.SequenceEqual(new[] { "DTR-Declared", "DTR-Evidence", "DTR-Undeclared" }),
            "[FAIL] deleted_finding_names_cannot_be_emitted: " + string.Join(", ", names));
    }
}
