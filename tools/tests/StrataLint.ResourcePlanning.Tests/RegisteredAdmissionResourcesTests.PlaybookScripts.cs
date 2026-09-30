using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("tools/scripts/workflow/playbook-workflows.sh")]
    public void PlaybookWorkflowRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("Makefile")]
    public void PlaybookMakefileRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/JudgeSeedTask.Tests/JudgeSeedTask.Tests.csproj",
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.BuildIntegration.Tests/StrataLint.BuildIntegration.Tests.csproj",
            "tools/tests/StrataLint.BuildRuntime.Tests/StrataLint.BuildRuntime.Tests.csproj",
            "tools/tests/StrataLint.Cache.Native.Tests/StrataLint.Cache.Native.Tests.csproj",
            "tools/tests/StrataLint.CheckIntegration.Tests/StrataLint.CheckIntegration.Tests.csproj",
            "tools/tests/StrataLint.CiArtifacts.Tests/StrataLint.CiArtifacts.Tests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.Configuration.Tests/StrataLint.Configuration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            "tools/tests/StrataLint.Digestion.Tests/StrataLint.Digestion.Tests.csproj",
            "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj",
            "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
            "tools/tests/StrataLint.ExecutionEvidence.Tests/StrataLint.ExecutionEvidence.Tests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.InspectionIntegration.Tests/StrataLint.InspectionIntegration.Tests.csproj",
            "tools/tests/StrataLint.InspectionScope.Tests/StrataLint.InspectionScope.Tests.csproj",
            "tools/tests/StrataLint.InstructionContract.Tests/StrataLint.InstructionContract.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.NativeTransportIntegration.Tests/StrataLint.NativeTransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.PlanningIntegration.Tests/StrataLint.PlanningIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseIntegration.Tests/StrataLint.ReleaseIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseSelection.Tests/StrataLint.ReleaseSelection.Tests.csproj",
            "tools/tests/StrataLint.RepositoryConfiguration.Tests/StrataLint.RepositoryConfiguration.Tests.csproj",
            "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj",
            "tools/tests/StrataLint.RepositoryDigestion.Tests/StrataLint.RepositoryDigestion.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.ResourcePlanning.Tests/StrataLint.ResourcePlanning.Tests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Documents.Tests/StrataLint.Scribe.Documents.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.SourceAtomizer.Tests/StrataLint.SourceAtomizer.Tests.csproj",
            "tools/tests/StrataLint.StageIntegration.Tests/StrataLint.StageIntegration.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.TransportIntegration.Tests/StrataLint.TransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj",
            "tools/tests/Trureturing.Truth.Tests/Trureturing.Truth.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/TestSupport/StrataLint.AdmissionTestSupport/TransactionFixture.cs")]
    public void PlaybookSharedFixtureRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/TestSupport/StrataLint.ProcessTestSupport/TestProcessRunner.cs")]
    public void PlaybookProcessSupportRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/TestSupport/StrataLint.TestSupport/TestScratchRoot.cs")]
    public void PlaybookScratchSupportRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/JudgeSeedTask.Tests/JudgeSeedTask.Tests.csproj",
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.BuildIntegration.Tests/StrataLint.BuildIntegration.Tests.csproj",
            "tools/tests/StrataLint.BuildRuntime.Tests/StrataLint.BuildRuntime.Tests.csproj",
            "tools/tests/StrataLint.Cache.Native.Tests/StrataLint.Cache.Native.Tests.csproj",
            "tools/tests/StrataLint.CheckIntegration.Tests/StrataLint.CheckIntegration.Tests.csproj",
            "tools/tests/StrataLint.CiArtifacts.Tests/StrataLint.CiArtifacts.Tests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.Configuration.Tests/StrataLint.Configuration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            "tools/tests/StrataLint.Digestion.Tests/StrataLint.Digestion.Tests.csproj",
            "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj",
            "tools/tests/StrataLint.ExecutionEvidence.Tests/StrataLint.ExecutionEvidence.Tests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.InspectionIntegration.Tests/StrataLint.InspectionIntegration.Tests.csproj",
            "tools/tests/StrataLint.InspectionScope.Tests/StrataLint.InspectionScope.Tests.csproj",
            "tools/tests/StrataLint.InstructionContract.Tests/StrataLint.InstructionContract.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.NativeTransportIntegration.Tests/StrataLint.NativeTransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.PlanningIntegration.Tests/StrataLint.PlanningIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseIntegration.Tests/StrataLint.ReleaseIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseSelection.Tests/StrataLint.ReleaseSelection.Tests.csproj",
            "tools/tests/StrataLint.RepositoryConfiguration.Tests/StrataLint.RepositoryConfiguration.Tests.csproj",
            "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj",
            "tools/tests/StrataLint.RepositoryDigestion.Tests/StrataLint.RepositoryDigestion.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.ResourcePlanning.Tests/StrataLint.ResourcePlanning.Tests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.SourceAtomizer.Tests/StrataLint.SourceAtomizer.Tests.csproj",
            "tools/tests/StrataLint.StageIntegration.Tests/StrataLint.StageIntegration.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.TransportIntegration.Tests/StrataLint.TransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/StrataLint.Engine/BoundedProcessRunner.cs")]
    public void PlaybookEngineRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/JudgeSeedTask.Tests/JudgeSeedTask.Tests.csproj",
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.BuildIntegration.Tests/StrataLint.BuildIntegration.Tests.csproj",
            "tools/tests/StrataLint.BuildRuntime.Tests/StrataLint.BuildRuntime.Tests.csproj",
            "tools/tests/StrataLint.CheckIntegration.Tests/StrataLint.CheckIntegration.Tests.csproj",
            "tools/tests/StrataLint.CiArtifacts.Tests/StrataLint.CiArtifacts.Tests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.Configuration.Tests/StrataLint.Configuration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            "tools/tests/StrataLint.Digestion.Tests/StrataLint.Digestion.Tests.csproj",
            "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj",
            "tools/tests/StrataLint.ExecutionEvidence.Tests/StrataLint.ExecutionEvidence.Tests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.InspectionIntegration.Tests/StrataLint.InspectionIntegration.Tests.csproj",
            "tools/tests/StrataLint.InspectionScope.Tests/StrataLint.InspectionScope.Tests.csproj",
            "tools/tests/StrataLint.InstructionContract.Tests/StrataLint.InstructionContract.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.NativeTransportIntegration.Tests/StrataLint.NativeTransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.PlanningIntegration.Tests/StrataLint.PlanningIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseIntegration.Tests/StrataLint.ReleaseIntegration.Tests.csproj",
            "tools/tests/StrataLint.RepositoryConfiguration.Tests/StrataLint.RepositoryConfiguration.Tests.csproj",
            "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj",
            "tools/tests/StrataLint.RepositoryDigestion.Tests/StrataLint.RepositoryDigestion.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Documents.Tests/StrataLint.Scribe.Documents.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.SourceAtomizer.Tests/StrataLint.SourceAtomizer.Tests.csproj",
            "tools/tests/StrataLint.StageIntegration.Tests/StrataLint.StageIntegration.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.TransportIntegration.Tests/StrataLint.TransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/Trureturing.Truth/TruthExportModel.cs")]
    public void PlaybookTruthRetainsEveryRegisteredConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(new[] {
            "tools/tests/JudgeSeedTask.Tests/JudgeSeedTask.Tests.csproj",
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.BuildIntegration.Tests/StrataLint.BuildIntegration.Tests.csproj",
            "tools/tests/StrataLint.BuildRuntime.Tests/StrataLint.BuildRuntime.Tests.csproj",
            "tools/tests/StrataLint.CheckIntegration.Tests/StrataLint.CheckIntegration.Tests.csproj",
            "tools/tests/StrataLint.CiArtifacts.Tests/StrataLint.CiArtifacts.Tests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.Configuration.Tests/StrataLint.Configuration.Tests.csproj",
            "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj",
            "tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            "tools/tests/StrataLint.Digestion.Tests/StrataLint.Digestion.Tests.csproj",
            "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj",
            "tools/tests/StrataLint.ExecutionEvidence.Tests/StrataLint.ExecutionEvidence.Tests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.InspectionIntegration.Tests/StrataLint.InspectionIntegration.Tests.csproj",
            "tools/tests/StrataLint.InspectionScope.Tests/StrataLint.InspectionScope.Tests.csproj",
            "tools/tests/StrataLint.InstructionContract.Tests/StrataLint.InstructionContract.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.NativeTransportIntegration.Tests/StrataLint.NativeTransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.PlanningIntegration.Tests/StrataLint.PlanningIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseIntegration.Tests/StrataLint.ReleaseIntegration.Tests.csproj",
            "tools/tests/StrataLint.ReleaseSelection.Tests/StrataLint.ReleaseSelection.Tests.csproj",
            "tools/tests/StrataLint.RepositoryConfiguration.Tests/StrataLint.RepositoryConfiguration.Tests.csproj",
            "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj",
            "tools/tests/StrataLint.RepositoryDigestion.Tests/StrataLint.RepositoryDigestion.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Documents.Tests/StrataLint.Scribe.Documents.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.SourceAtomizer.Tests/StrataLint.SourceAtomizer.Tests.csproj",
            "tools/tests/StrataLint.StageIntegration.Tests/StrataLint.StageIntegration.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.TransportIntegration.Tests/StrataLint.TransportIntegration.Tests.csproj",
            "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj",
            "tools/tests/Trureturing.Truth.Tests/Trureturing.Truth.Tests.csproj",
            }), Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }
}
