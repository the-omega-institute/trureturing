using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class ScribeTestMapDeriverTests
{
    [Fact]
    public void TemporaryFileSystemRootReadIsNotARepositoryInput()
    {
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource("tools/tests/SyntheticTests.cs", """
                public sealed class SyntheticTests
                {
                    [Fact]
                    public void ReadsSyntheticProjection()
                    {
                        var temporary = TemporaryFileSystem.Directory.CreateTempSubdirectory();
                        _ = TemporaryFileSystem.File.ReadAllBytes(
                            Path.Combine(temporary.FullName, "projection.json"));
                    }
                }
                """)],
            []);

        var method = Assert.Single(map.Methods);
        Assert.Equal("SyntheticTests.ReadsSyntheticProjection", method.Id);
        Assert.Empty(method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void RepositoryAccessorRootReadRemainsARepositoryInput()
    {
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource("tools/tests/SyntheticTests.cs", """
                public sealed class SyntheticTests
                {
                    [Fact]
                    public void ReadsRepositoryInput()
                    {
                        _ = RepositoryAccessor.ReadAllText(
                            RepositoryRelativePath.Create("Golden/input.txt"));
                    }
                }
                """)],
            []);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["Golden/input.txt"], method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void CrossTypeRepositoryHelperContributesDeclaredPath()
    {
        var map = Derive("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void ReadsThroughHelper() => RepositoryQueries.ReadInput();
            }

            internal static class RepositoryQueries
            {
                internal static void ReadInput() => RepositoryAccessor.ReadAllText(
                    RepositoryRelativePath.Create("Blueprint/D5/S0/Sample.scribe.cs"));
            }
            """);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["Blueprint/D5/S0/Sample.scribe.cs"], method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void ScannedReceiverWithMissingOrAmbiguousMethodFailsClosed()
    {
        var map = Derive("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void CallsMissingMethod() => RepositoryQueries.Missing();

                [Fact]
                public void CallsAmbiguousMethod() => RepositoryQueries.ReadInput();
            }

            internal static class RepositoryQueries
            {
                internal static void Existing() { }
                internal static void ReadInput() { }
                internal static void ReadInput(string ignored) { }
            }
            """);

        Assert.All(
            map.Methods,
            static method => Assert.Equal(
                TestMapUnknownReason.Other,
                Assert.Single(method.UnknownReasons)));
    }

    [Fact]
    public void ImplicitCallsMissingFromScannedReceiverFailClosed()
    {
        var map = Derive("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void CallsMissingMethod() => Missing();

                [Fact]
                public void CallsMissingMethodThroughThis() => this.AlsoMissing();
            }
            """);

        Assert.All(
            map.Methods,
            static method => Assert.Equal(
                TestMapUnknownReason.Other,
                Assert.Single(method.UnknownReasons)));
    }

    [Fact]
    public void OwnedMemberInitializerRepositoryHelperContributesDeclaredPath()
    {
        var map = Derive("""
            public sealed class SyntheticTests
            {
                private sealed class Fixture
                {
                    internal string Content { get; } = RepositoryQueries.ReadInput();
                }

                [Fact]
                public void UsesFixture() => Assert.NotNull(new Fixture().Content);
            }

            internal sealed class UnrelatedType
            {
                internal string Content { get; } = RepositoryQueries.ReadUnrelatedInput();
            }

            internal static class RepositoryQueries
            {
                internal static string ReadInput() => RepositoryAccessor.ReadAllText(
                    RepositoryRelativePath.Create("Blueprint/D5/S0/Sample.scribe.cs"));

                internal static string ReadUnrelatedInput() => RepositoryAccessor.ReadAllText(
                    RepositoryRelativePath.Create("Golden/unrelated.json"));
            }
            """);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["Blueprint/D5/S0/Sample.scribe.cs"], method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void UnscannedReceiverTypesDoNotCreateUnknownDebt()
    {
        var map = Derive("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void UsesExternalLibraries()
                {
                    Assert.Equal(1, Math.Abs(-1));
                    ThirdPartyVerifier.Verify();
                }
            }
            """);

        var method = Assert.Single(map.Methods);
        Assert.Empty(method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void UnknownMethodOnDiscoveredRepositoryAccessorFailsClosed()
    {
        var map = DeriveWithDiscovery("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void UsesUnknownAccessorMethod() => RepositoryAccessor
                    .Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                    .ReadLines(RepositoryRelativePath.Create("CLAUDE.md"));
            }
            """);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["CLAUDE.md"], method.Paths);
        Assert.Equal(TestMapUnknownReason.Other, Assert.Single(method.UnknownReasons));
    }

    [Fact]
    public void KnownMethodOnDiscoveredRepositoryAccessorRemainsKnown()
    {
        var map = DeriveWithDiscovery("""
            public sealed class SyntheticTests
            {
                [Fact]
                public void UsesKnownAccessorMethod() => RepositoryAccessor
                    .Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                    .ReadAllText(RepositoryRelativePath.Create("CLAUDE.md"));
            }
            """);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["CLAUDE.md"], method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    private static ScribeTestMap Derive(string source) => ScribeTestMapDeriver.DeriveSources(
        [new TestMapSource("tools/tests/SyntheticTests.cs", source)],
        []);

    private static ScribeTestMap DeriveWithDiscovery(string source) =>
        ScribeTestMapDeriver.DeriveSources(
        [
            new TestMapSource("tools/tests/SyntheticTests.cs", source),
            new TestMapSource("tools/tests/RepositoryAccessor.cs", """
                internal sealed class RepositoryAccessor
                {
                    internal static RepositoryAccessor Discover(RepositoryRootCriterion criterion) =>
                        null!;

                    private static bool Matches(string root, RepositoryRootCriterion criterion) =>
                        criterion switch
                        {
                            RepositoryRootCriterion.ClaudeDirectoryNotFound =>
                                File.Exists(Path.Combine(root, "CLAUDE.md")),
                            _ => false,
                        };
                }
                """),
        ],
        []);
}
