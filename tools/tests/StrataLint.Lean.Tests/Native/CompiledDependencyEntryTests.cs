using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

[Collection("Lean cold production integration")]
public sealed class CompiledDependencyEntryTests
{
    [Fact]
    public void ProductionEntryReadsValueUsersSeparatelyFromTypesAndImports() =>
        Run("test_production_entry_reads_value_users_separately_from_types_and_imports");

    [Fact]
    public void ProductionEntryNamesUnknownDeclarationWithoutAnExactCount() =>
        Run("test_production_entry_names_unknown_declaration_without_an_exact_count");

    private static void Run(string scenario)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/scripts/agent/research_readouts/test_compiled_dependencies.py"),
            "DependencyEntryTests." + scenario], root, TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, "[FAIL] " + scenario + ": "
            + Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
