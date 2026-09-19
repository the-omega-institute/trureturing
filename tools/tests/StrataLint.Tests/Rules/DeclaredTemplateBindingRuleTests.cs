using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateBindingRuleTests
{
    internal static DeltaRuleContext Delta(bool declared = false, bool added = false,
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
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta()), "DTR-Undeclared", AdmissionEffect.Observe);

    [Fact]
    public void new_validated_registration_observes() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(declared: true, added: true)), "DTR-Declared", AdmissionEffect.Observe);

    [Fact]
    public void changed_unresolved_registration_blocks() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(declared: true, invalid: true)), "DTR-Evidence", AdmissionEffect.Observe);

    [Fact]
    public void delta_missing_evidence_blocks() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(missing: true)), "DTR-Evidence", AdmissionEffect.Observe);

    [Fact]
    public void first_pin_selects_registration() =>
        Finding(DeclaredTemplateBindingRule.Evaluate(Delta(changed: false, firstPin: true)), "DTR-Undeclared", AdmissionEffect.Observe);

    [Theory]
    [InlineData("stale-input")]
    [InlineData("malformed-record")]
    [InlineData("wrong-version")]
    public void delta_invalid_evidence_blocks(string mutation)
    {
        var before = Files();
        var after = new Dictionary<string, string>(before) { [Registration] = before[Registration] + "-- changed\n" };
        var reports = Report(after, count: 1, declared: true).Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
        var evidence = reports[Registration].InformationTemplates!;
        var wire = JsonSerializer.SerializeToNode(evidence)!;
        if (mutation == "stale-input") wire["inputs"]![0]!["sha256"] = new string('0', 64);
        if (mutation == "malformed-record") wire["records"]![0]!.AsObject().Remove("certificate");
        if (mutation == "wrong-version") wire["compatibility_version"] = 1;
        reports[Registration] = reports[Registration] with
        {
            InformationTemplates = JsonSerializer.SerializeToElement(wire),
        };
        Finding(DeclaredTemplateBindingRule.Evaluate(Context(before, after, LeanAxiomReport.Create(reports), [Registration])),
            "DTR-Evidence", AdmissionEffect.Observe);
    }

    [Fact]
    public void delta_does_not_collect_unchanged_module_evidence()
    {
        var before = Files();
        var after = new Dictionary<string, string>(before) { [Registration] = before[Registration] + "-- changed\n" };
        var report = Report(after, count: 1);
        before["D5/S0/Carrier/Unchanged.lean"] = "-- no evidence for unchanged registrations\n";
        after["D5/S0/Carrier/Unchanged.lean"] = before["D5/S0/Carrier/Unchanged.lean"];
        Finding(DeclaredTemplateBindingRule.Evaluate(Context(before, after, report, [Registration])),
            "DTR-Undeclared", AdmissionEffect.Observe);
    }

    [Theory]
    [InlineData(RawChangeKind.Added)] // Git renames are normalized to deleted/added endpoints.
    [InlineData(RawChangeKind.Copied)]
    public void rename_and_copy_destinations_select_registrations(RawChangeKind kind)
    {
        var context = Delta(added: true, declared: true);
        var changes = RawChangeSet.CreateWithKinds(
            [("D5/S0/Carrier/OldRegistration.lean", RawChangeKind.Deleted), (Registration, kind)]);
        var renamed = DeltaRuleContext.Create(context.Current, context.Baseline, context.Policy,
            context.Lean, changes, context.MetaEvaluation);
        Finding(DeclaredTemplateBindingRule.Evaluate(renamed), "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void applicability_ignores_judge_changes_and_deleted_modules()
    {
        var before = Files();
        var after = new Dictionary<string, string>(before) { [Judge] = "-- implementation changed\n" };
        after.Remove(Registration);
        var context = Context(before, after, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()), [Judge, Registration]);
        Assert.False(DeclaredTemplateBindingRule.IsAffectedBy(context));
        Assert.Empty(DeclaredTemplateBindingRule.Evaluate(context));
    }

    [Fact]
    public void deleted_finding_names_cannot_be_emitted()
    {
        var contexts = new[]
        {
            Delta(),
            Delta(declared: true),
            Delta(declared: true, invalid: true),
            Delta(missing: true),
            DeclaredTemplateUnregisteredTests.Build(),
        };
        var names = contexts.SelectMany(context => DeclaredTemplateBindingRule.Evaluate(context))
            .Select(finding => finding.Message.Split(' ', 2)[0])
            .Distinct().Order(StringComparer.Ordinal).ToArray();
        Assert.True(names.SequenceEqual(new[] { "DTR-Declared", "DTR-Evidence", "DTR-Undeclared", "DTR-Unregistered" }),
            "[FAIL] deleted_finding_names_cannot_be_emitted: " + string.Join(", ", names));
    }
}
