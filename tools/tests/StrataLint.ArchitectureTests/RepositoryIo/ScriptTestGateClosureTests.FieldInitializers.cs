namespace StrataLint.ArchitectureTests;

public sealed partial class ScriptTestGateClosureTests
{
    private const string RegistryFixture =
        "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";

    [Fact]
    public void RegistryTestsDeclareFixtureReadThroughStaticFieldInitializers()
    {
        string[] testNames =
        [
            "RegistryCompilerDefersStoredByteCanonicalityToSnapshotWriteGate",
            "RegistryFailsClosedForInvalidSchemaOrYamlFeature",
            "RegistryLoadAssertCarriesTheFailureReasonNotJustTheOutcomeType",
        ];

        foreach (var testName in testNames)
        {
            var snapshot = WithFiles(
                CurrentSnapshot(),
                (
                    "tools/tests/StrataLint.ScriptTests/RegistryTests.cs",
                    RegistryTestSource(testName)),
                (
                    "tools/tests/StrataLint.ScriptTests/TestRegistry.cs",
                    TestRegistrySource()),
                (RegistryFixture, "schema_version: 1\n"));

            var closure = Derive(snapshot, []);

            Assert.Contains(RegistryFixture, closure.ExactPaths);
        }
    }

    private static string RegistryTestSource(string testName) => $$"""
        using Xunit;

        namespace StrataLint.Tests;

        public sealed class RegistryTests
        {
            private static readonly string CanonicalRegistry = TestRegistry.Canonical;

            [Fact]
            public void {{testName}}()
            {
                _ = CanonicalRegistry;
            }
        }
        """;

    private static string TestRegistrySource() => $$"""
        namespace StrataLint.Tests;

        internal static class TestRegistry
        {
            internal static readonly string Canonical = LoadRepository();

            private static string LoadRepository() => File.ReadAllText(Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "{{RegistryFixture}}"));
        }
        """;
}
