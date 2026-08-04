using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryAtomizerDataTests
{
    private const string Minimal = """
        schema_version = 1

        [[observer.claim_prefixes]]
        prefix = "**Known**"
        locator = "theorem/known"

        [[gict.genres]]
        token = "定理"
        kind = "theorem"

        [[gict.claim_prefixes]]
        prefix = "**Heart**"
        locator = "open/heart"

        [[gict.constants]]
        name = "κ"
        locator = "constant/kappa"

        [[pzg.genres]]
        token = "定理"
        kind = "theorem"

        [[pzg.markers]]
        role = "trace-note"
        text = "追注"

        [[pzg.heading_prefixes]]
        prefix = "Supplement "
        locator = "metadata/supplement"

        [[pzg.heading_prefixes]]
        prefix = "判负册"
        locator = "negative-register/batch"

        [[wm.headings]]
        role = "title"
        text = "Synthetic WM"

        [[wm.headings]]
        role = "appendix"
        text = "Synthetic appendix"

        [[wm.headings]]
        role = "audit"
        text = "Synthetic audit"
        """;

    public static TheoryData<string, string> InvalidData => new()
    {
        { "", "missing file" },
        { Minimal.Replace("schema_version = 1\n", "", StringComparison.Ordinal), "missing schema version" },
        { Minimal.Replace("schema_version = 1", "schema_version = 2", StringComparison.Ordinal), "unsupported schema version" },
        { Minimal.Replace("schema_version = 1", "schema_version = \"1\"", StringComparison.Ordinal), "non-integer schema version" },
        { Minimal.Replace("schema_version = 1", "schema_version = 1\nunknown = \"x\"", StringComparison.Ordinal), "unknown root key" },
        { Minimal.Replace("[[gict.constants]]\nname = \"κ\"\nlocator = \"constant/kappa\"\n", "", StringComparison.Ordinal), "missing required section" },
        { Minimal.Replace("prefix = \"**Known**\"\n", "", StringComparison.Ordinal), "missing required field" },
        { Minimal.Replace("prefix = \"**Known**\"", "prefix = \"**Known**\"\nextra = \"x\"", StringComparison.Ordinal), "unknown entry field" },
        { Minimal.Replace("prefix = \"**Known**\"", "prefix = \"\"", StringComparison.Ordinal), "empty string" },
        { Minimal.Replace("locator = \"theorem/known\"", "locator = \"bad locator\"", StringComparison.Ordinal), "invalid locator" },
        { Minimal.Replace("[[observer.claim_prefixes]]", "[[unknown.claim_prefixes]]", StringComparison.Ordinal), "unknown atomizer section" },
        { Minimal.Replace("prefix = \"**Known**\"", "prefix = \"**Known**\"\nprefix = \"again\"", StringComparison.Ordinal), "duplicate key" },
        { Minimal.Replace("[[gict.genres]]\ntoken = \"定理\"\nkind = \"theorem\"", "[[gict.genres]]\ntoken = \"定理\"\nkind = \"theorem\"\n\n[[gict.genres]]\ntoken = \"定理\"\nkind = \"theorem\"", StringComparison.Ordinal), "duplicate open key" },
        { Minimal.Replace("[[observer.claim_prefixes]]\nprefix = \"**Known**\"\nlocator = \"theorem/known\"", "[[observer.claim_prefixes]]\nprefix = \"**A**\"\nlocator = \"theorem/known\"\n\n[[observer.claim_prefixes]]\nprefix = \"**B**\"\nlocator = \"theorem/known\"", StringComparison.Ordinal), "duplicate locator without alias" },
        { Minimal.Replace("token = \"定理\"\nkind = \"theorem\"", "token = \"短\"\nkind = \"theorem\"\n\n[[pzg.genres]]\ntoken = \"更长\"\nkind = \"definition\"", StringComparison.Ordinal), "non-canonical order" },
    };

    [Theory]
    [MemberData(nameof(InvalidData))]
    public void LoaderRejectsMalformedData(string data, string _)
    {
        var snapshot = data.Length == 0
            ? Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(RawRepositorySnapshot.Create([]))).Snapshot
            : DigestionTestSupport.Snapshot((TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data)));
        Assert.Throws<FormatException>(() => TheoryAtomizerDataLoader.Load(snapshot));
    }

    [Fact]
    public void LoaderRejectsInvalidUtf8()
    {
        var snapshot = DigestionTestSupport.Snapshot((TheoryAtomizerDataLoader.DataPath, new byte[] { 0xff }));
        Assert.Throws<FormatException>(() => TheoryAtomizerDataLoader.Load(snapshot));
    }

    [Fact]
    public void SyntheticRulesChangeObserverGenreConstantAndHeadingRecognition()
    {
        var data = Load(Minimal
            .Replace("prefix = \"**Known**\"", "prefix = \"**New observer lead**\"", StringComparison.Ordinal)
            .Replace("token = \"定理\"", "token = \"新体裁\"", StringComparison.Ordinal)
            .Replace("name = \"κ\"", "name = \"NEW_C\"", StringComparison.Ordinal)
            .Replace("locator = \"constant/kappa\"", "locator = \"constant/new-c\"", StringComparison.Ordinal)
            .Replace("prefix = \"判负册\"", "prefix = \"新标题\"", StringComparison.Ordinal));

        Assert.Equal("theorem/known", Assert.Single(ObserverAtomizer.Atomize(Encoding.UTF8.GetBytes("**New observer lead** body"), data).Claims).AstPath);
        Assert.Equal("theorem/1.1", Assert.Single(GictAtomizer.Atomize(Encoding.UTF8.GetBytes("**新体裁 1.1** body"), data).Claims).AstPath);
        Assert.Equal("theorem/1.1", Assert.Single(PzgAtomizer.Atomize(Encoding.UTF8.GetBytes("**新体裁 1.1** body"), data).Claims).AstPath);
        Assert.Equal("constant/new-c", Assert.Single(GictAtomizer.Atomize(
            Encoding.UTF8.GetBytes("| Constant | Value |\n|---|---|\n| NEW_C | value |\n"), data).Claims).AstPath);
        Assert.Equal("negative-register/batch", Assert.Single(PzgAtomizer.Atomize(Encoding.UTF8.GetBytes("## 新标题 batch"), data).Claims).AstPath);
    }

    [Fact]
    public void PzgPatternAndKindMappingHaveExactlyOneSource()
    {
        var data = Load(Minimal.Replace("token = \"定理\"", "token = \"A+B\"", StringComparison.Ordinal));
        var atom = Assert.Single(PzgAtomizer.Atomize(Encoding.UTF8.GetBytes("**A+B 1.2** body"), data).Claims);
        Assert.Equal("theorem/1.2", atom.AstPath);
        Assert.All(data.PzgGenres, genre => Assert.True(PzgAtomizer.RecognizesGenre(genre.Token, data)));
    }

    [Fact]
    public void GictUnknownNumberedGenreStillFailsClosed()
    {
        var error = Assert.Throws<TheorySourceFormatException>(() => GictAtomizer.Atomize(
            Encoding.UTF8.GetBytes("**未知体裁 1.1** body"),
            Load(Minimal)));
        Assert.Contains("unknown GICT numbered claim kind", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionAtomizerContractHasNoRulesFreeEntryPoint()
    {
        var atomizeMethods = typeof(AtomizerRegistry).GetMethods(BindingFlags.Static | BindingFlags.NonPublic)
            .Where(method => method.Name == "Atomize").ToArray();
        Assert.Single(atomizeMethods);
        Assert.Equal(typeof(TheoryAtomizerRules), atomizeMethods[0].GetParameters()[2].ParameterType);
        Assert.Equal(2, typeof(TheoryAtomizer).GetMethod("Invoke")!.GetParameters().Length);
    }

    [Fact]
    public void LocatorKindAlphabetIsClosedInProgram()
    {
        Assert.Equal(
            new[] { "axiom", "consequence", "contract", "corollary", "criterion", "definition", "entry", "example", "extension-table", "frontier-note", "ledger", "lemma", "note", "observation", "principle", "proposition", "remark", "route", "specification", "survey", "theorem", "theorem-form" },
            TheoryAtomizerRules.AllowedKinds.Order(StringComparer.Ordinal));
    }

    private static TheoryAtomizerRules Load(string text) => TheoryAtomizerDataLoader.Load(
        DigestionTestSupport.Snapshot((TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(text))));
}
