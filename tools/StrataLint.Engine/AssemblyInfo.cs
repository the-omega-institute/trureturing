using System.Runtime.CompilerServices;

// Process and admission fixtures consume Engine's internal process and policy APIs.
[assembly: InternalsVisibleTo("StrataLint.ProcessTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.AdmissionTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.RepositoryFileMap.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Engine.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
[assembly: InternalsVisibleTo("StrataLint.Cache.Tests")]
[assembly: InternalsVisibleTo("StrataLint")]
[assembly: InternalsVisibleTo("StrataLint.Configuration")]
[assembly: InternalsVisibleTo("StrataLint.Configuration.Tests")]
[assembly: InternalsVisibleTo("StrataLint.RepositoryConfiguration.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Scribe")]
[assembly: InternalsVisibleTo("StrataLint.Scribe.Tests")]
[assembly: InternalsVisibleTo("StrataLint.EngineeringScope")]
[assembly: InternalsVisibleTo("StrataLint.Lean")]
[assembly: InternalsVisibleTo("StrataLint.Lean.Tests")]

[assembly: InternalsVisibleTo("StrataLint.InspectionScope")]

[assembly: InternalsVisibleTo("StrataLint.ExecutionEvidence")]

[assembly: InternalsVisibleTo("StrataLint.BuildRuntime")]

[assembly: InternalsVisibleTo("StrataLint.CliTestSupport")]

[assembly: InternalsVisibleTo("StrataLint.CliIntegration.Tests")]

[assembly: InternalsVisibleTo("StrataLint.FileMap")]

[assembly: InternalsVisibleTo("StrataLint.FileMap.Tests")]

[assembly: InternalsVisibleTo("StrataLint.PrScript.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ReportSupervisor.Tests")]
[assembly: InternalsVisibleTo("StrataLint.RuleTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.Rules.Tests")]
[assembly: InternalsVisibleTo("StrataLint.LeanReportScript.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ResourceObservation.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Digestion.Tests")]
[assembly: InternalsVisibleTo("StrataLint.DigestionTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.DeclaredTemplate.Tests")]
[assembly: InternalsVisibleTo("StrataLint.DeclaredTemplateTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.WorkflowScript.Tests")]
[assembly: InternalsVisibleTo("StrataLint.InstructionContract.Tests")]
[assembly: InternalsVisibleTo("StrataLint.RepositoryContract.Tests")]
[assembly: InternalsVisibleTo("StrataLint.RepositoryTopology.Tests")]
[assembly: InternalsVisibleTo("StrataLint.LeanCacheScript.Tests")]
[assembly: InternalsVisibleTo("StrataLint.RepositoryDigestion.Tests")]
