using System.Runtime.CompilerServices;

// Process and admission fixtures consume Engine's internal process and policy APIs.
[assembly: InternalsVisibleTo("StrataLint.ProcessTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.AdmissionTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Engine.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
[assembly: InternalsVisibleTo("StrataLint.Cache.Tests")]
[assembly: InternalsVisibleTo("StrataLint")]
[assembly: InternalsVisibleTo("StrataLint.Scribe")]
[assembly: InternalsVisibleTo("StrataLint.Scribe.Tests")]
[assembly: InternalsVisibleTo("StrataLint.EngineeringScope")]
[assembly: InternalsVisibleTo("StrataLint.Lean")]
[assembly: InternalsVisibleTo("StrataLint.Lean.Tests")]
