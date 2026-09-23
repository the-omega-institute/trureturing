using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CurrentDeltaCliContractTests
{
    private const string TemplateRegistrationPath = "Reg/" + RuleFixture.RingPath;
    private const string UnselectedRegistrationPath = "Reg/" + RuleFixture.ValuesBindingPath;
    private const string TemplateModule = "Reg.D5.S0.Carrier.Ring";
    private const string TemplateUnit = TemplateModule + ".unit";
    private const string TemplateTheorem = "Different.Namespace.ringResult";
    private const string TemplateTheoremSource = "\nnamespace Different.Namespace\n"
        + "theorem ringResult : goldenRing = 0 := rfl\nend Different.Namespace\n";

    private static void AddTemplateRegistrationFixtures(RuleFixture fixture)
    {
        fixture.Files[TemplateRegistrationPath] = "import D5.S0.Carrier.Ring\n"
            + $"def {TemplateUnit} : Nat := goldenRing\n";
        fixture.Reports[TemplateRegistrationPath] = new(["D5.S0.Carrier.Ring"],
            [new(TemplateUnit, "def", "Nat", [])]);
        fixture.Files[UnselectedRegistrationPath] = "import D5.S0.Carrier.ValuesBinding\n";
        fixture.Reports[UnselectedRegistrationPath] = new(["D5.S0.Carrier.ValuesBinding"], []);
    }

    // Synthetic compiler evidence exercises the real raw loader and CLI handoff;
    // it makes no kernel-proof claim. Reg owns the unit and imports its D5 realization.
    private static LeanAxiomReport TemplateReport(IReadOnlyDictionary<string, LeanFileReport> reports,
        string scenario)
    {
        var occurrence = new InformationOccurrenceKey(TemplateModule, TemplateModule,
            scenario.StartsWith("template-new-owner-", StringComparison.Ordinal) ? TemplateTheorem : "goldenRing",
            TemplateModule + ".arena", TemplateModule + ".catalog");
        return LeanAxiomReport.Create(reports.ToDictionary(pair => pair.Key, pair =>
        {
            if (pair.Key != TemplateRegistrationPath)
                return pair.Value with
                {
                    InformationTemplates = pair.Key == UnselectedRegistrationPath || scenario == "template-unchanged"
                        ? JsonSerializer.SerializeToElement("malformed unselected payload") : null,
                    InformationRegistrationErrors = ImmutableArray<string>.Empty,
                };
            var own = new[] { occurrence };
            var wire = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = 9,
                inventory = own.Select(InformationTemplateJson.KeyJson),
                registered = own.Select(InformationTemplateJson.KeyJson),
                records = own.Select(key => new
                {
                    key = InformationTemplateJson.KeyJson(key), registration_source_path = TemplateRegistrationPath,
                    statement_identity = InformationTemplateJson.Sha256(System.Text.Encoding.UTF8.GetBytes(key.Theorem)),
                    binding_source_path = (string?)null, state = "undeclared",
                    diagnostic = $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
                    escape_from = DeclaredTemplateEscapeRecordTests.FromSlot,
                    escape_continues = DeclaredTemplateEscapeRecordTests.OpenSlot, bridge_kind = "legacy",
                    unit_name = TemplateUnit, realization_name = "goldenRing", certificate = (object?)null,
                }),
            });
            return pair.Value with
            {
                InformationTemplates = scenario == "template-unchanged"
                    ? JsonSerializer.SerializeToElement("malformed unselected payload") : wire,
                InformationRegistrationErrors = ImmutableArray<string>.Empty,
            };
        }));
    }

    private void AssertTemplateDelta(string scenario, int expectedExit, string diagnostic, string output)
    {
        log.WriteLine(output);
        using var verdict = JsonDocument.Parse(output);
        var findings = verdict.RootElement.GetProperty("diagnostics").EnumerateArray().ToArray();
        var dtr = findings.Where(f => f.GetProperty("Message").GetString()!.StartsWith("DTR-", StringComparison.Ordinal)).ToArray();
        Assert.All(dtr, f =>
        {
            Assert.Equal("SL-031", f.GetProperty("RuleId").GetProperty("Value").GetString());
            Assert.Equal((int)AdmissionEffect.Observe, f.GetProperty("AdmissionEffect").GetInt32());
        });
        Assert.DoesNotContain(dtr, f => f.GetProperty("Path").GetString() == UnselectedRegistrationPath);
        if (scenario == "template-unchanged") Assert.Empty(dtr);
        else
        {
            var registration = Assert.Single(dtr, f => f.GetProperty("Path").GetString() == TemplateRegistrationPath);
            var message = registration.GetProperty("Message").GetString()!;
            Assert.StartsWith(diagnostic + " ", message, StringComparison.Ordinal);
            if (scenario.EndsWith("missing-evidence", StringComparison.Ordinal))
                Assert.Equal("DTR-Evidence DTR-Evidence: missing current producer for " + TemplateRegistrationPath, message);
            else
                Assert.Contains(TemplateModule, message, StringComparison.Ordinal);
            var newOwner = scenario.StartsWith("template-new-owner-", StringComparison.Ordinal);
            Assert.Equal(newOwner ? 2 : 1, dtr.Length);
            if (newOwner)
            {
                var unregistered = Assert.Single(dtr, f => f.GetProperty("Path").GetString() == RuleFixture.RingPath);
                Assert.Equal("DTR-Unregistered D5.S0.Carrier.Ring/" + TemplateTheorem,
                    unregistered.GetProperty("Message").GetString());
            }
        }

        // Changing unfrozen D5 still requires utility, independently of DTR Observe.
        var blockers = findings.Where(f => f.GetProperty("AdmissionEffect").GetInt32() != (int)AdmissionEffect.Observe).ToArray();
        if (expectedExit == 0) Assert.Empty(blockers);
        else
        {
            var blocker = Assert.Single(blockers);
            Assert.Equal("SL-031", blocker.GetProperty("RuleId").GetProperty("Value").GetString());
            Assert.Equal(RuleFixture.RingPath, blocker.GetProperty("Path").GetString());
            Assert.Equal((int)AdmissionEffect.Block, blocker.GetProperty("AdmissionEffect").GetInt32());
            Assert.Equal("UTILITY-MISSING module=" + RuleFixture.RingPath, blocker.GetProperty("Message").GetString());
        }
    }
}
