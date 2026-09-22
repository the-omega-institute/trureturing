using System.Runtime.CompilerServices;

// Scratch lifecycle internals are available only to their registered test consumers.
[assembly: InternalsVisibleTo("StrataLint.AdmissionTestSupport")]
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
[assembly: InternalsVisibleTo("StrataLint.Cache.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Engine.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Lean.Tests")]

[assembly: InternalsVisibleTo("StrataLint.ReleaseSelection.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ReleaseIntegration.Tests")]
