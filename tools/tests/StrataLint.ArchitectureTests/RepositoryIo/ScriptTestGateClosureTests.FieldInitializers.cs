namespace StrataLint.ArchitectureTests;

public sealed partial class ScriptTestGateClosureTests
{
    private const string RegistryFixture =
        "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";

    [Fact]
    public void ScribeTestMapDeclaresRegistryFixtureReadThroughStaticFieldInitializers()
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

    // 照真实链的形状写,不用内联字面量:真实的 TestRegistry 经一个 const 字段
    // RelativePath 间接给出路径(tools/tests/StrataLint.Tests/Rules/TestRegistry.cs),
    // 那多出的一跳与字段初始化器这条边一起,才是本层要覆盖的形态。
    private static string TestRegistrySource() => $$"""
        namespace StrataLint.Tests;

        internal static class TestRegistry
        {
            internal const string RelativePath = "{{RegistryFixture}}";

            internal static readonly string Canonical = LoadRepository();

            private static string LoadRepository() => File.ReadAllText(Path.Combine(
                TestRepositoryLayout.FindRoot(),
                RelativePath));
        }
        """;
}
