using Xunit;

namespace StrataLint.Lean.Tests;

// Native production consumers retain the ordinary cumulative guard.
// Keep their repository report fixtures out of parallel xUnit workers.
[CollectionDefinition("Lean cold production integration", DisableParallelization = true)]
public sealed class LeanColdIntegrationCollection;
