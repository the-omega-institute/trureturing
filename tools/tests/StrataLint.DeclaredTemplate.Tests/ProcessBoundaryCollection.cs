namespace StrataLint.DeclaredTemplate.Tests;

// Native producers share the canonical worktree cache. xUnit owns their
// scheduling; the production cache guard still rejects concurrent writers.
[CollectionDefinition("Lean cache environment", DisableParallelization = true)]
public sealed class ProcessBoundaryCollection;
