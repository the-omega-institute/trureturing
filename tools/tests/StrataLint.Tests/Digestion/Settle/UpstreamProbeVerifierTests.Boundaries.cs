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
}
