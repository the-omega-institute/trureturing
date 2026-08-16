using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class QdoGenreSuffixTests
{
    private const string QdoSuffixRule = """
        [[dialect.genre_suffix]]
        dialect = "qdo"
        suffix = "例"
        """;

    private static readonly (string Token, int Count, string Kind)[] Pr2096TokenMultiset =
    [
        ("定理", 205, "theorem"),
        ("定义", 75, "definition"),
        ("推论", 43, "corollary"),
        ("原理", 12, "principle"),
        ("命题", 11, "proposition"),
        ("例", 8, "example"),
        ("条件定理", 3, "theorem-form"),
        ("算法", 2, "algorithm"),
        ("猜想", 1, "observation"),
        ("特例", 1, "example"),
        ("反例", 1, "example"),
        ("关键反例", 1, "example"),
    ];

    [Fact]
    public void Pr2096HeadTokenMultisetHasNoUnregisteredGenres()
    {
        var (bytes, expectedPaths) = Pr2096Fixture();

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal(363, document.Claims.Length);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(expectedPaths, document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void AnUnlistedCompoundEndingInExampleHeadClosesTheProductiveClass()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 极小反例 40.1\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal("example/40.1", Assert.Single(document.Claims).AstPath);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ExactConditionTheoremGenreWinsBeforeSuffixResolution()
    {
        var bytes = Encoding.UTF8.GetBytes("# QDO\n\n## 条件定理 40.2\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, DigestionTestSupport.Rules);

        Assert.Equal("theorem-form/40.2", Assert.Single(document.Claims).AstPath);
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void RemovingTheSuffixRuleMakesThePr2096FixtureUnregisteredAgain()
    {
        var rules = LoadRules(RemoveQdoSuffixRule(CanonicalData));
        var (bytes, _) = Pr2096Fixture();

        var document = AtomizerRegistry.Atomize("dialect:qdo", bytes, rules);

        Assert.Equal(["关键反例", "反例", "特例"], document.UnregisteredGenres.ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void MigrationPreservesEveryPreviouslyAcceptedLocatorAndUntouchedTable()
    {
        var migrated = LoadRules(CanonicalData);
        var legacy = LoadRules(
            RemoveQdoSuffixRule(CanonicalData).TrimEnd('\n') + "\n\n" + LegacyExactRepresentatives + "\n");
        var legacyQdoTokens = new[]
        {
            "定理", "定义", "命题", "推论", "例", "算法", "关键反例", "原理", "特例", "条件定理", "猜想",
        };

        foreach (var token in legacyQdoTokens)
        {
            var bytes = Encoding.UTF8.GetBytes($"# QDO\n\n## {token} 41.1\n\n证。\n");
            var before = AtomizerRegistry.Atomize("dialect:qdo", bytes, legacy);
            var after = AtomizerRegistry.Atomize("dialect:qdo", bytes, migrated);
            Assert.Equal(Assert.Single(before.Claims).AstPath, Assert.Single(after.Claims).AstPath);
            Assert.Empty(before.UnregisteredGenres);
            Assert.Empty(after.UnregisteredGenres);
            Assert.Equal(bytes, after.Reassemble().ToArray());
        }

        Assert.Equal(legacy.ObserverClaimPrefixes.ToArray(), migrated.ObserverClaimPrefixes.ToArray());
        Assert.Equal(legacy.ConeClaimPrefixes.ToArray(), migrated.ConeClaimPrefixes.ToArray());
        Assert.Equal(legacy.GictGenres.ToArray(), migrated.GictGenres.ToArray());
        Assert.Equal(legacy.GictClaimPrefixes.ToArray(), migrated.GictClaimPrefixes.ToArray());
        Assert.Equal(legacy.GictConstants.ToArray(), migrated.GictConstants.ToArray());
        Assert.Equal(legacy.PzgGenres.ToArray(), migrated.PzgGenres.ToArray());
        Assert.Equal(legacy.PzgHeadingPrefixes.ToArray(), migrated.PzgHeadingPrefixes.ToArray());
        Assert.Equal(
            legacy.PzgMarkers.OrderBy(static item => item.Key).ToArray(),
            migrated.PzgMarkers.OrderBy(static item => item.Key).ToArray());
        Assert.Equal(
            legacy.WmHeadings.OrderBy(static item => item.Key).ToArray(),
            migrated.WmHeadings.OrderBy(static item => item.Key).ToArray());
        Assert.Equal(
            legacy.Dialects.Keys.Where(static id => id != "qdo").Order(StringComparer.Ordinal),
            migrated.Dialects.Keys.Where(static id => id != "qdo").Order(StringComparer.Ordinal));
    }

    [Fact]
    public void OverlappingSyntheticSuffixesResolveLongestFirst()
    {
        var data = InsertBefore(CanonicalData, "[[dialect.genre]]", LongestDialect + "\n\n");
        data = InsertBefore(data, "[[dialect.genre_suffix]]", LongestExactGenres + "\n\n");
        data = data.TrimEnd('\n') + "\n\n" + LongestSuffixes + "\n";
        var rules = LoadRules(data);
        var bytes = Encoding.UTF8.GetBytes("# Probe\n\n## 极新体 1.1\n\n证。\n\n## 极体 1.2\n\n证。\n");

        var document = AtomizerRegistry.Atomize("dialect:longest-probe", bytes, rules);

        Assert.Equal(
            ["observation/1.1", "theorem/1.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Empty(document.UnregisteredGenres);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    private static string CanonicalData => Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);

    private static TheoryAtomizerRules LoadRules(string data) => TheoryAtomizerDataLoader.Load(
        DigestionTestSupport.Snapshot(
            (TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data))));

    private static (byte[] Bytes, string[] ExpectedPaths) Pr2096Fixture()
    {
        var source = new StringBuilder("# QDO\n\n");
        var paths = new List<string>(363);
        var number = 1;
        foreach (var (token, count, kind) in Pr2096TokenMultiset)
        {
            for (var occurrence = 0; occurrence < count; occurrence++)
            {
                source.Append("## ").Append(token).Append(" 40.").Append(number).Append("\n\n证。\n\n");
                paths.Add($"{kind}/40.{number}");
                number++;
            }
        }

        Assert.Equal(363, paths.Count);
        Assert.Equal(12, Pr2096TokenMultiset.Length);
        return (Encoding.UTF8.GetBytes(source.ToString()), paths.ToArray());
    }

    private static string RemoveQdoSuffixRule(string data) => data.Replace(
        "\n\n" + QdoSuffixRule + "\n",
        "\n",
        StringComparison.Ordinal);

    private static string InsertBefore(string data, string marker, string insertion)
    {
        var index = data.IndexOf(marker, StringComparison.Ordinal);
        Assert.True(index >= 0, $"marker not found: {marker}");
        return data.Insert(index, insertion);
    }

    private const string LegacyExactRepresentatives = """
        [[dialect.genre]]
        dialect = "qdo"
        token = "关键反例"
        kind = "example"

        [[dialect.genre]]
        dialect = "qdo"
        token = "特例"
        kind = "example"
        """;

    private const string LongestDialect = """
        [[dialect]]
        id = "longest-probe"
        claim = "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+(?:\\.[0-9]+)+)"
        target = "heading"
        """;

    private const string LongestExactGenres = """
        [[dialect.genre]]
        dialect = "longest-probe"
        token = "体"
        kind = "theorem"

        [[dialect.genre]]
        dialect = "longest-probe"
        token = "新体"
        kind = "observation"
        """;

    private const string LongestSuffixes = """
        [[dialect.genre_suffix]]
        dialect = "longest-probe"
        suffix = "体"

        [[dialect.genre_suffix]]
        dialect = "longest-probe"
        suffix = "新体"
        """;
}
