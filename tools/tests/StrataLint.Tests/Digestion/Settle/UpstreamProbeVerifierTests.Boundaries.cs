using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class UpstreamProbeVerifierTests
{
    [Fact]
    public void RejectsProjectModuleEvenWhenPresentUnderPinnedPackage()
    {
        using var f = new ProbeFixture();
        var directory = Path.Combine(f.Root, ".lake/packages/mathlib/D5");
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "Injected.lean"), "", Encoding.UTF8);
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(Source.Replace("import Mathlib", "import D5.Injected", StringComparison.Ordinal)));
        Assert.Equal("PROBE_IMPORTS_PROJECT", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Theory]
    [InlineData("private theorem hidden : True := by trivial\n")]
    [InlineData("@[simp] theorem hidden : True := by trivial\n")]
    [InlineData("private lemma hidden : True := by trivial\n")]
    public void RejectsUnprintedProofsInUnsupportedDeclarationForms(string hidden)
    {
        using var f = new ProbeFixture();
        var source = Source.Replace("theorem probe", hidden + "theorem probe", StringComparison.Ordinal);
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(source));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void SupportsApostropheInTheoremName()
    {
        using var f = new ProbeFixture();
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(Output.Replace("probe", "probe'", StringComparison.Ordinal)), []));
        Assert.Equal(3, f.Verify(Source.Replace("probe", "probe'", StringComparison.Ordinal)).Length);
    }

    [Theory]
    [InlineData("meta import D5.Injected\n")]
    [InlineData("public import D5.Injected\n")]
    [InlineData("import\n D5.Injected\n")]
    [InlineData("import  \n D5.Injected\n")]
    [InlineData("import /- split -/\n D5.Injected\n")]
    [InlineData("import Mathlib -- trailing\n")]
    [InlineData("import Mathlib /- trailing -/\n")]
    [InlineData("import Mathlib.\n")]
    public void UnrecognizedImportSyntaxCannotHideAProjectImport(string import)
    {
        using var f = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(Source.Replace("theorem probe", import + "theorem probe", StringComparison.Ordinal)));
        Assert.Equal("PROBE_IMPORT_SYNTAX", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void RejectsUnknownAxiom()
    {
        using var f = new ProbeFixture();
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' depends on axioms: [secret]\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify());
        Assert.Equal("PROBE_AXIOMS", error.Code);
        Assert.Single(f.Runner.Sources);
    }

    [Fact]
    public void ResolverReportsEveryUnresolvedNameInRequestOrder()
    {
        using var f = new ProbeFixture();
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(Output), []));
        f.Runner.Results.Enqueue(new(1, Encoding.UTF8.GetBytes("file:3:8: error: True.intro\nfile:2:8: error: Nat.add_comm\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify());
        Assert.Equal("DECLARATION_UNRESOLVED", error.Code);
        Assert.StartsWith("Nat.add_comm unresolved=[Nat.add_comm,True.intro]", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("/- import Mathlib -/\n")]
    [InlineData("-- import Mathlib\n")]
    public void CommentImportsDoNotEstablishUpstreamClosure(string imports)
    {
        using var f = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(Source.Replace("import Mathlib\n", imports, StringComparison.Ordinal)));
        Assert.Equal("PROBE_IMPORTS_PROJECT", error.Code);
    }

    [Theory]
    [InlineData("def")]
    [InlineData("noncomputable def")]
    [InlineData("abbrev")]
    [InlineData("instance")]
    [InlineData("lemma")]
    [InlineData("example")]
    [InlineData("structure")]
    [InlineData("inductive")]
    [InlineData("opaque")]
    [InlineData("axiom")]
    [InlineData("macro")]
    [InlineData("elab")]
    [InlineData("syntax")]
    [InlineData("notation")]
    [InlineData("set_option")]
    [InlineData("namespace")]
    [InlineData("section")]
    [InlineData("variable")]
    [InlineData("universe")]
    [InlineData("attribute")]
    [InlineData("#eval")]
    [InlineData("#check")]
    public void RejectsEveryUnsupportedTopLevelFormBeforeExecution(string keyword)
    {
        using var f = new ProbeFixture();
        var source = Source.Replace("theorem probe", keyword + " hidden\ntheorem probe", StringComparison.Ordinal);
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(source));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Theory]
    [InlineData("theorem probe : True := by trivial\n  def hidden := 1\n#print axioms probe\n")]
    [InlineData("theorem probe : True := by trivial\n  theorem hidden : True := by trivial\n#print axioms probe\n")]
    [InlineData("  trivial\ntheorem probe : True := by trivial\n#print axioms probe\n")]
    public void IndentationCannotIntroduceAnotherCommand(string body)
    {
        using var f = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify("import Mathlib\n" + body));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Theory]
    [InlineData("def!", false)]
    [InlineData("def!", true)]
    [InlineData("def?", false)]
    [InlineData("def?", true)]
    [InlineData("def₁", false)]
    [InlineData("def₁", true)]
    [InlineData("theorem'", false)]
    [InlineData("theorem'", true)]
    public void ProofTermIdentifiersAreAcceptedAcrossLineBreaks(string name, bool indented)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe (" + name + " : True) : True :="
            + (indented ? "\n  " : " ") + name + "\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExplicitArgumentProofTermIsAcceptedAcrossLineBreaks(bool indented)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True :="
            + (indented ? "\n  " : " ") + "@True.intro\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData("@[simp] theorem s : True := trivial")]
    [InlineData("@[simp]")]
    public void IndentedAttributeOpenersAreRejected(string attribute) => AssertDialectRejected(
        "theorem probe : True := by\n  " + attribute + "\n  trivial\n#print axioms probe\n");

    [Fact]
    public void UnprintedDefinitionCannotHideItsAxioms()
    {
        using var f = new ProbeFixture();
        var source = Source.Replace("theorem probe", "noncomputable def unprinted : Nat := Classical.choice (inferInstance : Nonempty Nat)\ntheorem probe", StringComparison.Ordinal);
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' does not depend on any axioms\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(source));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void TheoremTextInsideStringIsNotAProofDeclaration()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ndef note := \"\ntheorem Nat.add_comm : True := by trivial\n\"\n#print axioms Nat.add_comm\n";
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'Nat.add_comm' does not depend on any axioms\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(source));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void CommentsAndEscapedStringsDoNotAddCommandsToTheoremInventory()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\n/- outer /- nested -/\ndef hidden := 1\n-/\nopen Nat\ntheorem probe : True := by\n  let note := \"escaped \\\" quote -- /-\ntheorem fake : True := by trivial\n#print axioms fake\n\"\n  trivial\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal("import Mathlib\n#check @Nat.add_comm\n#check @True.intro\n", f.Runner.Sources[1]);
    }

    [Theory]
    [InlineData("theorem probe : True := by trivial\n")]
    [InlineData("theorem probe : True := by trivial\n#print axioms probe\n#print axioms probe\n")]
    [InlineData("theorem probe : True := by trivial\n#print axioms other\n")]
    [InlineData("#print axioms Nat.add_comm\n")]
    [InlineData("theorem probe : True := by trivial\n#print axioms probe\ntheorem second : True := by trivial\n#print axioms second\n")]
    public void TheoremsAndTrailingPrintsMustBeInOneToOneCorrespondence(string body)
    {
        using var f = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify("import Mathlib\n" + body));
        Assert.Equal("PROBE_AXIOMS", error.Code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void AcceptsAnotherPinnedPackageModule()
    {
        using var f = new ProbeFixture();
        var directory = Path.Combine(f.Root, ".lake/packages/batteries");
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "Batteries.lean"), "", Encoding.UTF8);
        var manifest = Manifest.Replace("}]", "},{\"name\":\"batteries\",\"rev\":\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"}]", StringComparison.Ordinal);
        var result = new UpstreamProbeVerifier(f.Runner, "synthetic-lake", PinnedProductionBudgets.UpstreamProbeBudget)
            .Verify(f.Root, Encoding.UTF8.GetBytes(Source.Replace("import Mathlib", "import Batteries", StringComparison.Ordinal)), manifest, ["True.intro"]);
        Assert.Equal(3, result.Length);
    }

    public static IEnumerable<object[]> DottedKeywordReferences()
    {
        foreach (var name in new[]
                 {
                     "Polynomial.Monic.def", "IsBaseChange.end", "OneCocycle.class", "IsReduced.infix",
                     "Monic.def", "h.def", "Monic.theorem", "«def».end", "Monic.«def».end",
                     "«def.x».class", "def!.theorem"
                 })
        foreach (var apply in new[] { false, true })
            yield return [name, apply];
    }

    [Theory]
    [MemberData(nameof(DottedKeywordReferences))]
    public void DottedKeywordSegmentsDoNotCreateCommands(string name, bool apply)
    {
        using var f = new ProbeFixture();
        // Fake execution isolates token admission from the referenced declarations' types.
        var source = "import Mathlib\ntheorem probe (h : True) : True := "
            + (apply ? "by\n  exact (" + name + ").mp h" : name)
            + "\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData("«def»")]
    [InlineData("«def.x»")]
    [InlineData("Monic.«def»")]
    [InlineData("Monic.«#print»")]
    public void EscapedKeywordSegmentsRemainIdentifiers(string name)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True := " + name + "\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData(".def x := 1")]
    [InlineData("def.x := 1")]
    [InlineData("instance.y : True := True.intro")]
    [InlineData("example.foo : True := True.intro")]
    [InlineData("theorem.bar : True := True.intro")]
    public void LeadingKeywordSegmentsCannotHideCommands(string command)
    {
        foreach (var separator in new[] { " ", "\n  ", "\n", "\n  exact " })
            AssertDialectRejected("theorem probe : True := True.intro" + separator + command
                + "\n#print axioms probe\n");
    }

    [Theory]
    [InlineData("r\"def example\"")]
    [InlineData("r#\"a\"def\"b\"#")]
    [InlineData("r#\"a\"example\"b\"#")]
    [InlineData("r##\"a\"#def\"b\"##")]
    [InlineData("r###\"a\\\"def\"b\"###")]
    [InlineData("r#\"a\nexample #eval! -- /-\nb\"#")]
    public void RawStringLiteralsDoNotCreateCommandTokens(string literal)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : " + literal + " = " + literal
            + " := rfl\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData("'\"'")]
    [InlineData("'c'")]
    [InlineData("'\\n'")]
    [InlineData("'\\\\'")]
    [InlineData("'\\''")]
    [InlineData("'\\x22'")]
    [InlineData("'\\u{22}'")]
    [InlineData("'𝒜'")]
    public void CharacterLiteralsDoNotCreatePhantomStrings(string literal)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : (" + literal + " = " + literal
            + ") := rfl\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Fact]
    public void SingleQuoteCharacterDoesNotMaskTheRestOfTheProbe()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : '\"' = Char.ofNat 34 := rfl\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Fact]
    public void CharacterQuoteCannotMaskARealCommand() => AssertDialectRejected(
        "theorem probe : ('\"' = '\"') := rfl def hidden := 1\n#print axioms probe\n");

    [Theory]
    [InlineData("r#\"unterminated\"")]
    [InlineData("r##\"unterminated\"#")]
    public void UnterminatedRawStringIsRejected(string literal)
    {
        using var f = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(
            "import Mathlib\ntheorem probe : True := by\n  let note := " + literal
            + "\n  trivial\n#print axioms probe\n"));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Equal("unterminated string or block comment", error.Message);
        Assert.Empty(f.Runner.Sources);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(5)]
    public void ExtraHashAfterRawStringTerminatorRemainsACommand(int hashCount)
    {
        var hashes = new string('#', hashCount);
        // Lean closes at the first k hashes; the following #eval! is actual code.
        AssertDialectRejected("theorem probe : True := by\n  let note := r" + hashes
            + "\"a\"" + hashes + "#eval! (0 : Nat)\n  -- \"" + hashes
            + "\n  trivial\n#print axioms probe\n");
    }

    [Fact]
    public void TacticTraceCannotSpoofInventoriedAxiomOutput()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem t : True := by\n"
            + "  trace \"'t' depends on axioms: [propext]\"\n  trivial\n#print axioms t\n";
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(
            "'t' depends on axioms: [propext]\n"
            + "'t' depends on axioms: [propext]\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify(source));
        Assert.Equal("PROBE_AXIOMS", error.Code);
        Assert.Equal("duplicate axiom output", error.Message);
        Assert.Single(f.Runner.Sources);
        Assert.All(f.Runner.Paths, path => Assert.False(File.Exists(path)));
    }

}
