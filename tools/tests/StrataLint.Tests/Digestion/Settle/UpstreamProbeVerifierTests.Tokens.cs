using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class UpstreamProbeVerifierTests
{
    [Fact]
    public void SameLineTrailingCommandIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro def hidden := 1\n#print axioms probe\n");

    [Fact]
    public void SameLineSecondTheoremIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro theorem hidden (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms probe\n");

    [Fact]
    public void IndentedInitializeIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro\n  initialize hidden : Nat ← pure 1\n#print axioms probe\n");

    [Fact]
    public void IndentedNonrecDefIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro\n  nonrec def hidden := 1\n#print axioms probe\n");

    [Theory]
    [InlineData("def")]
    [InlineData("lemma")]
    [InlineData("example")]
    [InlineData("instance")]
    [InlineData("abbrev")]
    [InlineData("structure")]
    [InlineData("inductive")]
    [InlineData("class")]
    [InlineData("opaque")]
    [InlineData("axiom")]
    [InlineData("initialize")]
    [InlineData("nonrec")]
    [InlineData("noncomputable")]
    [InlineData("unsafe")]
    [InlineData("partial")]
    [InlineData("private")]
    [InlineData("protected")]
    [InlineData("macro")]
    [InlineData("macro_rules")]
    [InlineData("elab")]
    [InlineData("syntax")]
    [InlineData("notation")]
    [InlineData("infix")]
    [InlineData("infixl")]
    [InlineData("infixr")]
    [InlineData("prefix")]
    [InlineData("postfix")]
    [InlineData("set_option")]
    [InlineData("namespace")]
    [InlineData("section")]
    [InlineData("end")]
    [InlineData("variable")]
    [InlineData("universe")]
    [InlineData("attribute")]
    [InlineData("deriving")]
    [InlineData("mutual")]
    [InlineData("open")]
    [InlineData("#eval")]
    [InlineData("#check")]
    [InlineData("#reduce")]
    [InlineData("#exit")]
    [InlineData("run_cmd")]
    [InlineData("run_tac")]
    [InlineData("builtin_initialize")]
    [InlineData("declare_syntax_cat")]
    [InlineData("register_option")]
    [InlineData("import")]
    public void CommandKeywordIsRejectedAtEveryPositionAfterHeader(string keyword)
    {
        foreach (var separator in new[] { " ", "\n  ", "\n", "\n  exact " })
            AssertDialectRejected("theorem probe : True := True.intro" + separator
                + keyword + " hidden\n#print axioms probe\n");
    }

    [Theory]
    [InlineData("theorem probe : True := True.intro #print axioms probe\n#print axioms probe\n")]
    [InlineData("theorem probe : True := True.intro\n  exact (#print axioms probe)\n#print axioms probe\n")]
    [InlineData("theorem probe : True := True.intro\n  exact (theorem hidden : True := True.intro)\n#print axioms probe\n")]
    public void TheoremAndPrintTokensMustStartAtColumnZero(string body) => AssertDialectRejected(body);

    [Fact]
    public void TacticWordsContainingKeywordPrefixesAreAccepted()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\nopen Nat\ntheorem probe : True → True := by\n"
            + "  intro definitely\n  let defer : Nat := default\n  exact definitely\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData("def'")]
    [InlineData("def!")]
    [InlineData("def?")]
    [InlineData("def₁")]
    [InlineData("defα")]
    [InlineData("αdef")]
    [InlineData("def𝒜")]
    [InlineData("𝒜def")]
    [InlineData("_def")]
    [InlineData("def1")]
    [InlineData("theorem'")]
    [InlineData("imported")]
    public void LeanIdentifierContinuationsDoNotCreateCommandTokens(string name)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True := by\n  let " + name
            + " : Nat := 1\n  trivial\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Fact]
    public void MaskedCommandTokensDoNotAffectTheoremOrPrintCounts()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True := by\n"
            + "  /- initialize /- theorem -/ #print axioms -/\n"
            + "  let note := \"nonrec def theorem #print axioms\"\n"
            + "  trivial -- theorem initialize #print axioms\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    private static void AssertDialectRejected(string body)
    {
        using var f = new ProbeFixture();
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' does not depend on any axioms\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify("import Mathlib\n" + body));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }
}
