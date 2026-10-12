using Xunit;

namespace StrataLint.Lean.Tests;

// Production compiled-FIB consumers use the repository's cold report route.
// Keep that root-mutating route out of parallel xUnit workers; each Python
// behavior still owns its private fixture and retains the original guard.
[CollectionDefinition("Lean cold production integration", DisableParallelization = true)]
public sealed class LeanColdIntegrationCollection;
