using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Lean.Tests;

public sealed class DependentFamilyNativeTests(DependentFamilyNativeFixture fixture)
    : IClassFixture<DependentFamilyNativeFixture>
{
    private static void Declared(string name, InformationTemplateOccurrence occurrence)
    {
        Assert.True(occurrence.HasFourSlots);
        var finding = DeclaredTemplateBindingRule.EvaluateOccurrence(DependentFamilyNativeFixture.Source(name), occurrence);
        Assert.Equal(AdmissionEffect.Observe, finding.Effect);
        Assert.StartsWith("DTR-Declared ", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void unchanged_original_and_imported_sidecar_preserve_exact_source_and_four_slots()
    {
        var original = Path.Combine(fixture.Root, DependentFamilyNativeFixture.Prefix + "DependentFamilyOriginal.lean");
        Assert.Equal("cd723f7bf18b41abdca6d69252c308d0b5c985abff488d488b75879c6cf80a80",
            Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(original))).ToLowerInvariant());
        var declaration = Assert.Single(fixture.Report.Files[DependentFamilyNativeFixture.Source("DependentFamilyOriginal")]
            .Declarations.Where(d => d.Name.EndsWith(".history_law_conditional_expectation", StringComparison.Ordinal)));
        Assert.Equal("sha256:4dfcc42642a4f4a9a426f2d6d816398deb58de5a19db99293644bc6ed51fc6f7",
            declaration.PrecomputedStatementId);
        // Declaration IDs include the module path. Recompute the original D5
        // address from the actual native material, without rewriting any source
        // or changing the fixture report that crosses the strict reader.
        var originalPath = RepoPath.CreateKnown("D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.lean");
        Assert.Equal("sha256:3877f924171137f82ba8cacfa7064d7996a799487be4aeba4d3a86624e219847",
            CanonicalStatementWriter.DeclarationStatementId(originalPath,
                declaration with { PrecomputedStatementId = null }));
        foreach (var name in new[] { "DependentFamily", "DependentFamilySidecar" })
        {
            var occurrence = fixture.Collect(name);
            Declared(name, occurrence);
            Assert.Equal(new[] { 0, 1, 11 }, occurrence.Family!.Coordinates);
            var material = fixture.Payload(name).GetProperty("records")[0].GetProperty("family_binding").GetProperty("material");
            Assert.Equal(13, material.GetProperty("telescope").GetArrayLength());
            Assert.Equal(6, material.GetProperty("telescope").EnumerateArray().Count(b =>
                b.GetProperty("binder_info").GetString() == "Lean.BinderInfo.instImplicit"));
            Assert.Equal(new[] { "u_1", "u_2" }, material.GetProperty("rigid_levels").EnumerateArray().Select(l => l.GetString()));
            Assert.Equal("open", material.GetProperty("continuation").GetString());
        }
    }

    [Fact]
    public void jointly_retargeting_both_native_rows_cannot_reuse_the_registration_certificate()
    {
        var changes = new[] { "DependentFamily", "DependentFamilySidecar" }.Select(name =>
        {
            var payload = JsonNode.Parse(fixture.Payload(name).GetRawText())!;
            var record = payload["records"]![0]!;
            record["unit_name"] = "LeanInformationAudit.Tests.DependentFamily.bad";
            record["realization_name"] = "LeanInformationAudit.Tests.DependentFamily.bad";
            return (name, JsonSerializer.SerializeToElement(payload));
        }).ToArray();
        var report = fixture.Change(changes);
        foreach (var name in new[] { "DependentFamily", "DependentFamilySidecar" })
            Assert.Contains("family registration identity mismatch",
                Assert.Throws<FormatException>(() => fixture.Collect(name, report)).Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("existing-def")]
    [InlineData("absent-def")]
    [InlineData("owner")]
    [InlineData("type")]
    [InlineData("body")]
    [InlineData("constant")]
    public void fully_rehashed_family_evidence_must_match_the_actual_native_declaration(string mutation)
    {
        const string registration = "LeanInformationAudit.Tests.DependentFamily.registration";
        var changes = new[] { "DependentFamily", "DependentFamilySidecar" }.Select(name =>
        {
            var payload = JsonNode.Parse(fixture.Payload(name).GetRawText())!;
            var record = payload["records"]![0]!;
            var material = record["family_binding"]!["material"]!;
            var certificate = record["certificate"]!;
            var input = Assert.Single(certificate["extraction_inputs"]!.AsArray(),
                value => value!["name"]!.GetValue<string>() == registration)!;
            switch (mutation)
            {
                case "existing-def":
                case "absent-def":
                    var target = mutation == "existing-def"
                        ? "LeanInformationAudit.Tests.DependentFamily.template"
                        : "LeanInformationAudit.Tests.DependentFamily.noSuchDefinition";
                    record["unit_name"] = target;
                    record["realization_name"] = target;
                    material["registration_name"] = target;
                    input["name"] = target;
                    break;
                case "owner": input["owner"] = "LeanInformationAudit.Tests.RegistrationGates.DependentFamilySidecar"; break;
                case "type": input["type_identity"] = new string('0', 64); break;
                case "body": input["body_identity"] = new string('0', 64); break;
                case "constant": material["registration_identity"] = new string('0', 64); break;
            }
            var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(material));
            record["family_binding"]!["identity"] = identity;
            record["escape_from"]!["scope_identity"] = identity;
            certificate["evidence_ref"] = InformationFamilyEvidence.BindingIdentity(
                InformationTemplateJson.ReadKey(JsonSerializer.SerializeToElement(record["key"])),
                record["statement_identity"]!.GetValue<string>(), identity,
                JsonSerializer.SerializeToElement(certificate));
            return (name, JsonSerializer.SerializeToElement(payload));
        }).ToArray();
        var report = fixture.Change(changes);
        foreach (var name in new[] { "DependentFamily", "DependentFamilySidecar" })
        {
            Declared(name, fixture.Collect(name));
            Assert.Equal(fixture.Report.Files[DependentFamilyNativeFixture.Source(name)].Declarations,
                report.Files[DependentFamilyNativeFixture.Source(name)].Declarations);
            var error = Assert.Throws<FormatException>(() => fixture.Collect(name, report));
            Assert.Contains(mutation == "absent-def" ? "retained unit/realization owner"
                : "family registration declaration identity", error.Message, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("owner")]
    [InlineData("type_identity")]
    [InlineData("body_identity")]
    [InlineData("registration_identity")]
    [InlineData("level_arity")]
    [InlineData("level-kind")]
    [InlineData("schema")]
    public void selected_family_requires_current_native_declaration_evidence(string mutation)
    {
        var report = LeanAxiomReport.Create(fixture.Report.Files.ToDictionary(pair => pair.Key.Value, pair =>
            pair.Value with { Declarations = pair.Value.Declarations.Select(declaration =>
            {
                if (declaration.Name != "LeanInformationAudit.Tests.DependentFamily.registration") return declaration;
                var native = JsonNode.Parse(declaration.FamilyRegistration!.Value.GetRawText())!;
                if (mutation == "level_arity") native[mutation] = 1;
                else if (mutation == "level-kind") native["level_arity"] = "2";
                else native[mutation] = mutation == "owner" ? "Wrong.Owner"
                    : mutation == "schema" ? "statement-v1" : new string('0', 64);
                return declaration with { FamilyRegistration = mutation == "missing"
                    ? null : JsonSerializer.SerializeToElement(native) };
            }).ToImmutableArray() }));
        foreach (var name in new[] { "DependentFamily", "DependentFamilySidecar" })
            Assert.Throws<FormatException>(() => fixture.Collect(name, report));
        Declared("DependentFamilyFixedControl", fixture.Collect("DependentFamilyFixedControl", report));
    }

    [Fact]
    public void unresolved_native_family_preserves_evidence_verdict_and_exact_law_diagnostic()
    {
        var occurrence = fixture.Collect("DependentFamilyUnresolved");
        Assert.Equal(InformationTemplateBindingState.DeclaredUnresolved, occurrence.State);
        Assert.Null(occurrence.Family);
        Assert.Null(occurrence.EvidenceRef);
        Assert.False(occurrence.HasFourSlots);
        var finding = DeclaredTemplateBindingRule.EvaluateOccurrence(
            DependentFamilyNativeFixture.Source("DependentFamilyUnresolved"), occurrence);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Equal("DTR-Evidence " + occurrence.Diagnostic, finding.Message);
        Assert.Contains("family.registration.exact_source_law", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void supplementary_unicode_source_and_rigid_levels_cross_the_native_managed_boundary()
    {
        var occurrence = fixture.Collect("DependentFamilyUnicode");
        Declared("DependentFamilyUnicode", occurrence);
        Assert.EndsWith(".𝒜", occurrence.Key.Theorem, StringComparison.Ordinal);
        var material = fixture.Payload("DependentFamilyUnicode").GetProperty("records")[0]
            .GetProperty("family_binding").GetProperty("material");
        Assert.Equal(new[] { "𝒰", "𝒱" }, material.GetProperty("rigid_levels").EnumerateArray().Select(l => l.GetString()));
    }

    [Fact]
    public void coherent_unicode_retarget_to_existing_typed_registration_is_rejected()
    {
        var payload = JsonNode.Parse(fixture.Payload("DependentFamilyUnicode").GetRawText())!;
        var record = payload["records"]![0]!;
        var material = record["family_binding"]!["material"]!;
        var certificate = record["certificate"]!;
        const string original = "LeanInformationAudit.Tests.DependentFamilyUnicode.registration";
        const string target = "LeanInformationAudit.Tests.DependentFamily.registration";
        var actual = fixture.Report.Files[DependentFamilyNativeFixture.Source("DependentFamily")]
            .Declarations.Single(declaration => declaration.Name == target).FamilyRegistration!.Value;
        record["unit_name"] = target;
        record["realization_name"] = target;
        material["registration_name"] = target;
        material["registration_identity"] = actual.GetProperty("registration_identity").GetString();
        var input = Assert.Single(certificate["extraction_inputs"]!.AsArray(),
            value => value!["name"]!.GetValue<string>() == original)!;
        input["name"] = target;
        foreach (var field in new[] { "owner", "type_identity", "body_identity" })
            input[field] = actual.GetProperty(field).GetString();
        var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(material));
        record["family_binding"]!["identity"] = identity;
        record["escape_from"]!["scope_identity"] = identity;
        certificate["evidence_ref"] = InformationFamilyEvidence.BindingIdentity(
            InformationTemplateJson.ReadKey(JsonSerializer.SerializeToElement(record["key"])),
            record["statement_identity"]!.GetValue<string>(), identity,
            JsonSerializer.SerializeToElement(certificate));
        var report = fixture.Change(("DependentFamilyUnicode", JsonSerializer.SerializeToElement(payload)));
        var error = Assert.Throws<FormatException>(() => fixture.Collect("DependentFamilyUnicode", report));
        Assert.Contains("family source relation mismatch", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void unresolved_family_cannot_be_promoted_by_transplanting_full_certificate()
    {
        var donor = JsonNode.Parse(fixture.Payload("DependentFamily").GetRawText())!["records"]![0]!;
        var payload = JsonNode.Parse(fixture.Payload("DependentFamilyUnresolved").GetRawText())!;
        var record = payload["records"]![0]!;
        const string weakened = "LeanInformationAudit.Tests.DependentFamilyControls.weakenedRegistration";
        var actual = fixture.Report.Files[DependentFamilyNativeFixture.Source("DependentFamilyControls")]
            .Declarations.Single(declaration => declaration.Name == weakened).FamilyRegistration!.Value;
        record["state"] = "declared_validated";
        record["diagnostic"] = null;
        foreach (var field in new[] { "certificate", "family_binding", "escape_from" })
            record[field] = donor[field]!.DeepClone();
        record["certificate"]!["key"] = record["key"]!.DeepClone();
        var material = record["family_binding"]!["material"]!;
        material["registration_name"] = weakened;
        material["registration_identity"] = actual.GetProperty("registration_identity").GetString();
        var input = Assert.Single(record["certificate"]!["extraction_inputs"]!.AsArray(),
            value => value!["name"]!.GetValue<string>() ==
                "LeanInformationAudit.Tests.DependentFamily.registration")!;
        input["name"] = weakened;
        foreach (var field in new[] { "owner", "type_identity", "body_identity" })
            input[field] = actual.GetProperty(field).GetString();
        var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(material));
        record["family_binding"]!["identity"] = identity;
        record["escape_from"]!["scope_identity"] = identity;
        record["certificate"]!["evidence_ref"] = InformationFamilyEvidence.BindingIdentity(
            InformationTemplateJson.ReadKey(JsonSerializer.SerializeToElement(record["key"])),
            record["statement_identity"]!.GetValue<string>(), identity,
            JsonSerializer.SerializeToElement(record["certificate"]));
        var report = fixture.Change(("DependentFamilyUnresolved", JsonSerializer.SerializeToElement(payload)));
        var error = Assert.Throws<FormatException>(() => fixture.Collect("DependentFamilyUnresolved", report));
        Assert.Contains("family source relation mismatch", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("dropped-source")]
    [InlineData("dropped-levels")]
    [InlineData("captured-coordinate")]
    [InlineData("dictionary-coordinate")]
    [InlineData("substituted-origin")]
    [InlineData("raw-missing-origin")]
    [InlineData("wrong-law")]
    [InlineData("witness-scope")]
    [InlineData("cross-mode")]
    [InlineData("copied-plan")]
    [InlineData("stale-source")]
    [InlineData("rehashed-family")]
    [InlineData("rehashed-registration")]
    [InlineData("old-report")]
    public void source_bound_native_mutations_fail_closed(string mutation)
    {
        var payload = JsonNode.Parse(fixture.Payload("DependentFamily").GetRawText())!;
        var record = payload["records"]![0]!;
        var material = record["family_binding"]!["material"]!;
        switch (mutation)
        {
            case "old-report": payload["compatibility_version"] = 9; break;
            case "dropped-source": material.AsObject().Remove("source_name"); break;
            case "dropped-levels": material.AsObject().Remove("rigid_levels"); break;
            case "captured-coordinate": material["coordinates"] = new JsonArray(0, 1, 13); break;
            case "dictionary-coordinate": material["coordinates"] = new JsonArray(0, 1, 2, 11); break;
            case "substituted-origin": record["escape_from"]!["source"] = "Other.theorem"; break;
            case "raw-missing-origin": record["escape_from"] = null; break;
            case "wrong-law": material["law_identity"] = new string('0', 64); break;
            case "witness-scope": material["sensitivity_identity"] = new string('0', 64); break;
            case "cross-mode": record["key"]!["mode"] = "fixed-state-v1"; break;
            case "copied-plan": record["certificate"]!["plan_identity"] = new string('0', 64); break;
            case "stale-source": material["source_sha256"] = new string('0', 64); break;
            case "rehashed-registration":
                material["registration_name"] = "LeanInformationAudit.Tests.DependentFamily.bad";
                record["unit_name"] = material["registration_name"]!.DeepClone();
                record["realization_name"] = material["registration_name"]!.DeepClone();
                goto case "rehashed-family";
            case "rehashed-family":
                material["variation_identity"] = new string('0', 64);
                var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(material));
                record["family_binding"]!["identity"] = identity;
                record["escape_from"]!["scope_identity"] = identity;
                break;
        }
        var report = fixture.Change(("DependentFamily", JsonSerializer.SerializeToElement(payload)));
        Assert.Throws<FormatException>(() => fixture.Collect("DependentFamily", report));
    }

    [Fact]
    public void fixed_state_native_evidence_and_unselected_family_rows_keep_delta_scope()
    {
        var fixedOccurrence = fixture.Collect("DependentFamilyFixedControl");
        Declared("DependentFamilyFixedControl", fixedOccurrence);
        Assert.Equal("fixed-state-v1", fixedOccurrence.Key.Mode);
        Assert.Null(fixedOccurrence.Family);
        var payload = JsonNode.Parse(fixture.Payload("DependentFamily").GetRawText())!;
        payload["records"]![0]!["state"] = "invalid";
        var report = fixture.Change(("DependentFamily", JsonSerializer.SerializeToElement(payload)));
        Declared("DependentFamilyFixedControl", fixture.Collect("DependentFamilyFixedControl", report));
        Assert.Throws<FormatException>(() => fixture.Collect("DependentFamily", report));
    }
}
