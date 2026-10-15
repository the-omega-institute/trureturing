using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("", "unchanged", true)]
    [InlineData("", "value", false)]
    [InlineData("", "unrelated", true)]
    [InlineData("noncomputable ", "unchanged", true)]
    [InlineData("noncomputable ", "value", false)]
    [InlineData("noncomputable ", "unrelated", true)]
    [InlineData("@[irreducible] ", "unchanged", true)]
    [InlineData("@[irreducible] ", "value", false)]
    [InlineData("@[irreducible] ", "unrelated", true)]
    public void MathlibReanchorTracksInlineDefinitionCommands(string prefix, string mutation, bool authorized)
    {
        var source = "namespace N\ndef first : Nat := 1 " + prefix + "def value : Nat := 7\nend N\n";
        var root = ModuleWithReport("A", source, "old inline definition", declarations: ["N.value"], kind: "def");
        var candidate = root with
        {
            Source = mutation switch
            {
                "value" => source.Replace("value : Nat := 7", "value : Nat := 8", StringComparison.Ordinal),
                "unrelated" => source.Replace("first : Nat := 1", "first : Nat := 2", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new inline definition",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("value", false)]
    [InlineData("unrelated", true)]
    public void MathlibReanchorResolvesInlinePrivateNumericDefinitions(string mutation, bool equal)
    {
        const string source = "namespace N\nprivate noncomputable def c0 : Int := -10 "
            + "private noncomputable def c1 : Int := -7\nend N\n";
        const string name = "ns(ns(nn(ns(ns(ns(ns(ns(n0,8:_private),2:D5),2:S0),7:Carrier),1:A),0),1:N),2:c1)";
        var declarations = ImmutableArray.Create(new FrozenDeclaration(name, "def"));
        var baseline = LeanSourceCatalog.Parse(Snapshot([TextFile(PathFor("A"), source)]))
            .ExtractPropositionSource(RepoPathFor("A"), declarations);
        var candidateSource = mutation switch
        {
            "value" => source.Replace("c1 : Int := -7", "c1 : Int := -8", StringComparison.Ordinal),
            "unrelated" => source.Replace("c0 : Int := -10", "c0 : Int := -11", StringComparison.Ordinal),
            _ => source,
        };
        var candidate = LeanSourceCatalog.Parse(Snapshot([TextFile(PathFor("A"), candidateSource)]))
            .ExtractPropositionSource(RepoPathFor("A"), declarations);
        Assert.Equal(equal, baseline.SequenceEqual(candidate));
    }

    [Theory]
    [InlineData("unchanged", true)]
    [InlineData("proof", true)]
    [InlineData("statement", false)]
    public void MathlibReanchorKeepsInlineTheoremProofsOutsideStatementSources(string mutation, bool authorized)
    {
        const string source = "namespace N\ndef first : Nat := 1 theorem value : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old inline theorem", declarations: ["N.value"]);
        var candidate = root with
        {
            Source = mutation switch
            {
                "proof" => source.Replace("by trivial", "by exact True.intro", StringComparison.Ordinal),
                "statement" => source.Replace(": True :=", ": True ∧ True :=", StringComparison.Ordinal),
                _ => source,
            },
            StatementMaterial = "new inline theorem",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("end Inner end Outer", false)]
    [InlineData("end Inner end Outer", true)]
    [InlineData("end end", false)]
    [InlineData("end end", true)]
    [InlineData("end Inner end", false)]
    [InlineData("end Inner end", true)]
    [InlineData("end end Outer", false)]
    [InlineData("end end Outer", true)]
    public void MathlibReanchorResolvesConsecutiveInlineScopeEnds(string endings, bool changeValue)
    {
        var source = "namespace Outer\nnamespace Inner\ndef seed : Nat := 1\n" + endings
            + "\nnamespace Outer\ndef value : Nat := 7\nend Outer\n";
        var root = ModuleWithReport("A", source, "old inline scope end", declarations: ["Outer.value"], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace("value : Nat := 7", "value : Nat := 8", StringComparison.Ordinal) : source,
            StatementMaterial = "new inline scope end",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeValue, result.Authorized);
    }

    [Theory]
    [InlineData("def hidden : Nat := 1", "N.hidden", "def")]
    [InlineData("private noncomputable def hidden : Nat := 1", "N.hidden", "def")]
    [InlineData("namespace Wrong", "N.Wrong.real", "theorem")]
    [InlineData("end N", "real", "theorem")]
    [InlineData("end N end Wrong", "real", "theorem")]
    public void MathlibReanchorKeepsInlineQuotedCommandsOutOfRealRoots(
        string quoted, string falseName, string kind)
    {
        var source = "open Lean\nnamespace N\ndef quoted : MacroM (TSyntax `command) := `(command| "
            + quoted + ")\ntheorem real : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old actual root", declarations: ["N.real"]);
        var accepted = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new actual root" }, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(accepted.Authorized);
        var falseRoot = ModuleWithReport("A", source, "old false root", declarations: [falseName], kind: kind);
        var rejected = ValidateMathlibReanchor([falseRoot, Module("B")],
            [falseRoot with { StatementMaterial = "new false root" }, Module("B")], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(rejected.Authorized);
    }

    [Theory]
    [InlineData("end")]
    [InlineData("def")]
    [InlineData("theorem")]
    [InlineData("private")]
    [InlineData("public")]
    [InlineData("meta")]
    public void MathlibReanchorKeepsKeywordNameLiteralsInsideTheirCommands(string name)
    {
        var source = "import Lean\nnamespace N\ndef quoted : Lean.Name := `" + name
            + "\ntheorem real : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old name literal neighbour", declarations: ["N.real"]);
        var result = ValidateMathlibReanchor([root, Module("B")],
            [root with { StatementMaterial = "new name literal neighbour" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(result.Authorized);
    }

    [Theory]
    [InlineData("end", "def", false)]
    [InlineData("end", "def", true)]
    [InlineData("def", "theorem", false)]
    [InlineData("def", "theorem", true)]
    [InlineData("private", "protected", false)]
    [InlineData("private", "protected", true)]
    [InlineData("public", "meta", false)]
    [InlineData("public", "meta", true)]
    [InlineData("noncomputable", "partial", false)]
    [InlineData("noncomputable", "partial", true)]
    [InlineData("Nat", "Bool", false)]
    [InlineData("Nat", "Bool", true)]
    public void MathlibReanchorPreservesKeywordNameLiteralValues(string name, string replacement, bool changeValue)
    {
        var source = "import Lean\nnamespace N\ndef quoted : Lean.Name := `" + name + "\nend N\n";
        var root = ModuleWithReport("A", source, "old name literal", declarations: ["N.quoted"], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace("`" + name, "`" + replacement, StringComparison.Ordinal) : source,
            StatementMaterial = "new name literal",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeValue, result.Authorized);
    }

    public static IEnumerable<object[]> MathlibReanchorSectionHeaders()
    {
        for (var mask = 0; mask < 16; mask++)
        {
            var header = ((mask & 1) != 0 ? "@[expose] " : "")
                + ((mask & 2) != 0 ? "public " : "")
                + ((mask & 4) != 0 ? "noncomputable " : "")
                + ((mask & 8) != 0 ? "meta " : "") + "section";
            yield return [header, false];
            yield return [header, true];
        }
    }

    [Theory]
    [MemberData(nameof(MathlibReanchorSectionHeaders))]
    public void MathlibReanchorPreservesSectionHeaderPrefixes(string header, bool changeValue)
    {
        var source = "module\npublic import Lean\nnamespace N\n" + header
            + "\ndef value : Nat := 7\nend\ndef real : Nat := 8\nend N\n";
        var root = ModuleWithReport("A", source, "old section neighbour", declarations: ["N.real"], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace("real : Nat := 8", "real : Nat := 9", StringComparison.Ordinal) : source,
            StatementMaterial = "new section neighbour",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeValue, result.Authorized);
    }

    [Theory]
    [InlineData("end", false)]
    [InlineData("end", true)]
    [InlineData("def", false)]
    [InlineData("def", true)]
    [InlineData("private", false)]
    [InlineData("private", true)]
    public void MathlibReanchorKeepsEscapedKeywordsOutOfNeighbourScopes(string name, bool changeValue)
    {
        var source = "import Lean\nnamespace N\ndef «" + name
            + "» : Nat := 7\ntheorem real : True := by trivial\nend N\n";
        var root = ModuleWithReport("A", source, "old escaped name", declarations: ["N." + name], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace(": Nat := 7", ": Nat := 8", StringComparison.Ordinal) : source,
            StatementMaterial = "new escaped name",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized); // Escaped root-name resolution remains unsupported.
        var neighbour = ModuleWithReport("A", source, "old escaped neighbour", declarations: ["N.real"]);
        var neighbourResult = ValidateMathlibReanchor([neighbour, Module("B")],
            [neighbour with { StatementMaterial = "new escaped neighbour" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.True(neighbourResult.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesWholeEscapedIdentifierSpans(bool changeValue)
    {
        const string source = "namespace N\ndef value («x end y» : Nat) : Nat := «x end y»\nend N\n";
        var root = ModuleWithReport("A", source, "old escaped span", declarations: ["N.value"], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace(":= «x end y»", ":= Nat.succ «x end y»", StringComparison.Ordinal) : source,
            StatementMaterial = "new escaped span",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeValue, result.Authorized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorPreservesDotKeywordConstructorValues(bool changeValue)
    {
        const string source = "import Lean\nnamespace N\ndef value : Lean.Elab.DefKind := .def\nend N\n";
        var root = ModuleWithReport("A", source, "old dot constructor", declarations: ["N.value"], kind: "def");
        var candidate = root with
        {
            Source = changeValue ? source.Replace(".def", ".theorem", StringComparison.Ordinal) : source,
            StatementMaterial = "new dot constructor",
        };
        var result = ValidateMathlibReanchor([root, Module("B")], [candidate, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeValue, result.Authorized);
    }
}
