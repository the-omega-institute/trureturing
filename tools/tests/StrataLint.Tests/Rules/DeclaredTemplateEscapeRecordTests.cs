using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateEscapeRecordTests
{
    internal static object FromSlot => new { name = "Bool", type_identity = new string('a', 64), object_identity = new string('b', 64) };
    internal static object OpenSlot => new { kind = "open", declaration_name = (string?)null,
        statement_identity = (string?)null, chain_name = (string?)null };

    internal static DeltaRuleContext Slots(DeltaRuleContext context, string mode)
    {
        var reports = context.Lean.Report.Files.ToDictionary(p => p.Key.Value, p => p.Value);
        foreach (var (path, report) in reports.ToArray())
        {
            if (report.InformationTemplates is not { } payload) continue;
            var wire = JsonSerializer.SerializeToNode(payload)!;
            foreach (var record in wire["records"]!.AsArray())
            {
                record!["escape_from"] = mode == "old" ? null : JsonSerializer.SerializeToNode(FromSlot);
                record["escape_continues"] = mode == "old" ? null : JsonSerializer.SerializeToNode(OpenSlot);
                record["bridge_kind"] = mode is "witness" or "forward" or "unknown" ? mode : "legacy";
                if (mode == "malformed") record["escape_continues"]!["kind"] = "guessed";
            }
            if (mode == "two" && wire["records"]!.AsArray().Count > 0)
            {
                var second = wire["records"]![0]!.DeepClone();
                second["key"]!["object_arena"] = "D5.S0.Carrier.Target.secondArena";
                second["certificate"]!["key"] = second["key"]!.DeepClone();
                wire["records"]!.AsArray().Add(second);
                wire["inventory"]!.AsArray().Add(second["key"]!.DeepClone());
                wire["registered"]!.AsArray().Add(second["key"]!.DeepClone());
            }
            reports[path] = report with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
        }
        return DeltaRuleContext.Create(context.Current, context.Baseline, context.Policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(reports)), context.Changes, context.MetaEvaluation);
    }

    [Fact]
    public void selected_old_form_is_undeclared()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(
            DeclaredTemplateBindingRuleTests.Delta(declared: true), "old"));
        Assert.True(findings.Length == 1 && findings[0].Message.StartsWith("DTR-Undeclared ", StringComparison.Ordinal)
            && findings[0].Effect == AdmissionEffect.Block, "[FAIL] selected_old_form_is_undeclared");
    }

    [Fact]
    public void unchanged_old_form_is_not_read() => Assert.True(DeclaredTemplateBindingRule.Evaluate(Slots(
        DeclaredTemplateBindingRuleTests.Delta(declared: true, changed: false), "malformed")).IsEmpty,
        "[FAIL] unchanged_old_form_is_not_read");

    [Fact]
    public void new_theorem_requires_four_slots()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(DeclaredTemplateUnregisteredTests.Build(binding: "inline"), "old"));
        Assert.True(findings.Any(f => f.Message.StartsWith("DTR-Unregistered ", StringComparison.Ordinal)
            && f.Effect == AdmissionEffect.Block), "[FAIL] new_theorem_requires_four_slots");
    }

    [Fact]
    public void one_four_slot_registration_covers_theorem()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(DeclaredTemplateUnregisteredTests.Build(binding: "inline"), "full"));
        Assert.True(findings.Length == 1 && findings[0].Effect == AdmissionEffect.Observe
            && findings[0].Message.Contains("escape_from=", StringComparison.Ordinal)
            && findings[0].Message.Contains("escape_continues=", StringComparison.Ordinal)
            && findings[0].Message.Contains("bridge_kind=legacy", StringComparison.Ordinal),
            "[FAIL] one_four_slot_registration_covers_theorem: " + string.Join("; ", findings.Select(f => f.Message)));
    }

    [Fact]
    public void two_arenas_allow_two_registrations()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(DeclaredTemplateUnregisteredTests.Build(binding: "inline"), "two"));
        Assert.True(findings.Length == 2 && findings.All(f => f.Message.StartsWith("DTR-Declared ", StringComparison.Ordinal)
            && f.Effect == AdmissionEffect.Observe), "[FAIL] two_arenas_allow_two_registrations");
    }

    [Fact]
    public void malformed_escape_evidence_blocks()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(DeclaredTemplateUnregisteredTests.Build(binding: "inline"), "malformed"));
        Assert.True(findings.Any(f => f.Message.StartsWith("DTR-Evidence ", StringComparison.Ordinal)
            && f.Effect == AdmissionEffect.Block), "[FAIL] malformed_escape_evidence_blocks");
    }

    [Theory]
    [InlineData("legacy")]
    [InlineData("forward")]
    [InlineData("witness")]
    public void bridge_vocabulary_preserves_declared_verdict(string kind)
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(
            DeclaredTemplateUnregisteredTests.Build(binding: "inline"), kind));
        var finding = Assert.Single(findings);
        Assert.Equal(AdmissionEffect.Observe, finding.Effect);
        Assert.Contains("bridge_kind=" + kind, finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void unknown_bridge_kind_blocks_selected_only()
    {
        var findings = DeclaredTemplateBindingRule.Evaluate(Slots(
            DeclaredTemplateBindingRuleTests.Delta(declared: true), "unknown"));
        Assert.Contains(findings, f => f.Effect == AdmissionEffect.Block
            && f.Message.Contains("unknown bridge_kind", StringComparison.Ordinal));
        Assert.Empty(DeclaredTemplateBindingRule.Evaluate(Slots(
            DeclaredTemplateBindingRuleTests.Delta(declared: true, changed: false), "unknown")));
    }
}
