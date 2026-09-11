using System.Text;
using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Current source compiler")]
public sealed class SourceContextProducerTests(SourceCompilerFixture compiler)
{
    [Theory]
    [InlineData("test_import_visibility_matches_actual_importer")]
    [InlineData("test_command_boundaries_and_scopes")]
    [InlineData("test_errors_are_immediate_and_sticky")]
    [InlineData("test_registration_source_is_data_and_scope_is_measured")]
    [InlineData("test_option_wrapper_preserves_nested_command_scope")]
    public void CurrentCompilerSourceContract(string contract)
    {
        if (contract != "test_import_visibility_matches_actual_importer")
        {
            RunContract(contract);
            return;
        }
        using var temporary = new TemporaryDirectory();
        using var prepared = JsonDocument.Parse(RunImportOperation("--prepare-import-contract", temporary.Path));
        foreach (var source in prepared.RootElement.GetProperty("sources").EnumerateArray())
            _ = RunImportOperation("--compile-import", temporary.Path, source.GetString()!);
        var comparisons = prepared.RootElement.GetProperty("comparisons").GetInt32();
        Assert.Equal(15, comparisons);
        for (var index = 0; index < comparisons; index++)
            _ = RunImportOperation("--check-import", temporary.Path, index.ToString(System.Globalization.CultureInfo.InvariantCulture));
    }

    private byte[] RunImportOperation(params string[] arguments)
    {
        var result = TestProcessRunner.Run("python3", ["-c", SourceContextContractScript.Source, compiler.Root, .. arguments],
            compiler.Root, BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        return result.StandardOutput;
    }

    [Fact]
    public void InitOnlyGenuineCharUsesActualCompilerContext()
    {
        var run = TestProcessRunner.Run("python3", ["-c", SourceContextContractScript.Source, compiler.Root, "--init-contexts"],
            compiler.Root, BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(run.ExitCode == 0, Encoding.UTF8.GetString(run.StandardOutput) + Encoding.UTF8.GetString(run.StandardError));
        using var result = JsonDocument.Parse(run.StandardOutput);
        var rows = result.RootElement.EnumerateArray().ToArray();
        Assert.Equal(2, rows.Length);
        Assert.All(rows, entry =>
        {
            var source = entry.GetProperty("source").GetString()!;
            var path = RepoPath.CreateKnown("D5/Query.lean");
            var file = new RepositoryFile(path, Encoding.UTF8.GetBytes(source).ToImmutableArray(), source);
            var snapshot = RepositorySnapshot.Create(ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(path, file));
            var row = new JsonObject {
                ["side"] = "current", ["path"] = path.Value,
                ["sourceSha256"] = LeanSourceContextInput.SourceHash(file),
                ["producerSha256"] = LeanSourceContextInput.ProducerHash(snapshot),
                ["configurationSha256"] = LeanSourceContextInput.ConfigurationHash(snapshot),
                ["graphSha256"] = LeanSourceContextInput.GraphHash(snapshot, path),
                ["interfaces"] = new JsonArray(),
                ["result"] = JsonNode.Parse(entry.GetProperty("result").GetRawText()),
            };
            var bundle = new JsonObject { ["schema"] = LeanSourceContextInput.Schema, ["files"] = new JsonArray(row) };
            var input = LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(bundle.ToJsonString()), snapshot, snapshot);
            Assert.Empty(NativeDecideSourceRule.Inspect(snapshot, path, input));
        });
    }

    [Fact]
    public void PinnedPackageModuleOwnershipMustBeUnambiguous()
        => RunPreparationContract("test_duplicate_package_module_is_unknown");

    [Fact]
    public void FailedCompilerCannotBecomeReusableSourceContext()
        => RunPreparationContract("test_failed_compiler_is_not_a_cached_context");

    [Fact]
    public void SimpAttributesPreserveTokensWithoutElaboratingProtectedTargets()
        => RunContract("test_simp_attributes_do_not_elaborate_targets_or_change_tokens");

    [Fact]
    public void NotationExpansionStringsDoNotRegisterTokens()
        => RunContract("test_notation_expansion_strings_do_not_register_tokens");

    [Fact]
    public void DeclarationTokensRetainCompilerLocality()
        => RunContract("test_declaration_tokens_retain_compiler_locality");

    [Fact]
    public void InstanceAttributesPreserveTokensWithoutElaboratingProtectedTargets()
        => RunContract("test_instance_attributes_do_not_elaborate_targets_or_change_tokens");

    [Fact]
    public void UnmodeledAttributeProducesLocatedRefusal()
        => RunContract("test_unmodeled_attribute_is_a_located_error");

    private void RunPreparationContract(string contract)
    {
        var result = TestProcessRunner.Run("python3", ["-c", SourceContextContractScript.Source, compiler.Root,
            "PreparationContract." + contract], compiler.Root,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    private void RunContract(string contract)
    {
        var root = compiler.Root;
        var result = TestProcessRunner.Run("python3", ["-c", SourceContextContractScript.Source, root, "ProducerContract." + contract], root,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
