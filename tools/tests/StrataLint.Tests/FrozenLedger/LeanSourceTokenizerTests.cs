using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanSourceTokenizerTests
{
    [Theory]
    [InlineData(false, "g'")]
    [InlineData(true, "g'")]
    [InlineData(false, "a'")]
    [InlineData(true, "a'")]
    public void EqualityAmbiguityRetainsDependencyProjection(bool embedded, string name)
    {
        var tokens = Scan("open scoped FirstOrder\nt ='" + name, embedded)[3..];
        Assert.Equal(new[] { "t", "='", name }, tokens.Select(static token => token.Text));
        Assert.True(tokens[^1].IsIdentifier);
        Assert.Equal(2, tokens[^1].Line);
        Assert.Equal(4, tokens[^1].Column);

        // Exercise the existing dependency consumer with both scanner outputs.
        var identifiers = LeanSourceCatalog.QualifiedIdentifiers(tokens);
        Assert.Equal(new[] { "t", name }, identifiers);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityAmbiguityKeepsRealCharactersInertAndPositioned(bool embedded)
    {
        var tokens = Scan("\n'g' ='g'", embedded);
        Assert.Equal(new[] { "'g'", "=", "'g'" }, tokens.Select(static token => token.Text));
        Assert.All(tokens, token => Assert.False(token.IsIdentifier));
        Assert.Empty(LeanSourceCatalog.QualifiedIdentifiers(tokens));
        Assert.Equal(2, tokens[^1].Line);
        Assert.Equal(5, tokens[^1].Column);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void RegisteredDependentCompositionPreservesPrimedIdentifier(bool embedded, bool spaced)
    {
        var tokens = Scan("f \u2218'" + (spaced ? " " : "") + "g'", embedded);
        Assert.Equal(new[] { "f", "\u2218'", "g'" }, tokens.Select(static token => token.Text));
        Assert.False(tokens[1].IsIdentifier);
        Assert.Equal("g'", tokens[2].Identifier);
        Assert.Equal(1, tokens[2].Line);
        Assert.Equal(spaced ? 5 : 4, tokens[2].Column);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RegisteredPrefixAndInfixPrimesPreserveFollowingNames(bool embedded)
    {
        foreach (var term in new[] { "\u00d7'", "\u2295'", "\u03a3'", "\u2200'", "\u2203'", "#'" })
        {
            var tokens = Scan(term + "g'", embedded);
            Assert.Equal(new[] { term, "g'" }, tokens.Select(static token => token.Text));
            Assert.False(tokens[0].IsIdentifier);
            Assert.Equal("g'", tokens[1].Identifier);
            Assert.Equal(2, tokens[1].Column);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MultiCharacterPrimedPrefixesUseTheCompleteRegisteredSpelling(bool embedded)
    {
        foreach (var prefix in new[] { "\u03a3\u2097'", "\u207b\u00b9'", "\u207b\u00b9'o", "''\u1d41" })
        {
            var tokens = Scan(prefix + "g'", embedded);
            Assert.Equal(new[] { prefix, "g'" }, tokens.Select(static token => token.Text));
            Assert.False(tokens[0].IsIdentifier);
            Assert.Equal("g'", tokens[1].Identifier);
            Assert.Equal(prefix.Length, tokens[1].Column);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void BracketedPrimedNotationKeepsBracketAndIdentifierTokens(bool embedded)
    {
        foreach (var prefix in new[] { "\u2211'", "\u220f'", "\u227a'", "\u227c'", "\u2118'" })
        {
            var tokens = Scan(prefix + "[g']", embedded);
            Assert.Equal(new[] { prefix, "[", "g'", "]" }, tokens.Select(static token => token.Text));
            Assert.Equal("g'", tokens[2].Identifier);
            Assert.Equal(3, tokens[2].Column);
            var malformed = Assert.Throws<LeanSourceExtractionException>(() => Scan(prefix + "[g')", embedded));
            Assert.Equal("Lean delimiters are unbalanced.", malformed.Message);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrimedClosingDelimiterPreservesProofIdentifierAndDelimiterTracking(bool embedded)
    {
        var tokens = Scan("xs[i]'h'", embedded);
        Assert.Equal(new[] { "xs", "[", "i", "]", "'", "h'" }, tokens.Select(static token => token.Text));
        Assert.Equal("h'", tokens[^1].Identifier);
        Assert.Equal(6, tokens[^1].Column);
        var malformed = Assert.Throws<LeanSourceExtractionException>(() => Scan("xs(i]'h'", embedded));
        Assert.Equal("Lean delimiters are unbalanced.", malformed.Message);
        Assert.Equal(new[] { "f", "\u27e6", "n", "\u27e7'", "g'" },
            Scan("f\u27e6n\u27e7'g'", embedded).Select(static token => token.Text));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityPrimeRecognizesUnambiguousNotationAndPreservesRealCharacters(bool embedded)
    {
        foreach (var source in new[] { "=' right'", "='right'" })
        {
            var tokens = Scan("open scoped FirstOrder\n" + source, embedded)[3..];
            Assert.Equal(new[] { "='", "right'" }, tokens.Select(static token => token.Text));
            Assert.Equal("right'", tokens[1].Identifier);
        }

        // Outside the FirstOrder scope these are equality followed by a Char.
        foreach (var literal in new[] { "'a'", "')'", "' '", "'\\''", "'\\x61'", "'\\u0061'", "'\U0001f600'" })
        {
            var tokens = Scan("=" + literal, embedded);
            Assert.Equal(new[] { "=", literal }, tokens.Select(static token => token.Text));
            Assert.False(tokens[1].IsIdentifier);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityPrimeDoesNotHideMalformedCharacterEscape(bool embedded)
    {
        var error = Assert.Throws<LeanSourceExtractionException>(() => Scan("\n='\\u00xz'", embedded));
        Assert.Equal(2, error.Line);
        Assert.Equal("Lean character escape is malformed.", error.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdentifierLikePrimesKeepExistingIdentifierProjection(bool embedded)
    {
        foreach (var name in new[] { "\u2118'", "\u03c0'", "\U0001d4d3'", "\U0001d4e2'", "haveI'" })
        {
            Assert.Equal(name, Assert.Single(Scan(name, embedded)).Identifier);
        }
    }

    [Theory]
    [InlineData("\u227a'a")]
    [InlineData("\u227c'a")]
    [InlineData("\u2260'a")]
    [InlineData("+'a")]
    [InlineData(":='a")]
    public void IncompleteOrUnregisteredPrimedPrefixesRemainMalformedCharacters(string source)
    {
        foreach (var embedded in new[] { false, true })
        {
            var exception = Assert.Throws<LeanSourceExtractionException>(() => Scan("\n" + source, embedded));
            Assert.Equal(2, exception.Line);
            Assert.Equal("Lean character literal is unterminated or malformed.", exception.Message);
        }
    }


    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, false)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, false, true)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public void EqualityContextPreservesWholeIdentifierSpans(bool embedded, bool qualified, bool spaced)
    {
        var name = qualified ? "g'.native_decide" : "g'native_decide";
        var tokens = Scan("open scoped FirstOrder\n(t ='" + (spaced ? " " : "") + name + ")\nnative_decide", embedded);
        var reference = Assert.Single(tokens, token => token.Text == name);
        Assert.Equal(name, reference.Identifier);
        Assert.Equal(2, reference.Line);
        Assert.Equal(spaced ? 6 : 5, reference.Column);
        var bare = Assert.Single(tokens, token => token.Text == "native_decide");
        Assert.Equal(3, bare.Line);
        Assert.Equal(0, bare.Column);
    }

    [Theory]
    [InlineData("open scoped FirstOrder\n", "", true)]
    [InlineData("open FirstOrder\n", "", true)]
    [InlineData("namespace FirstOrder.Language\n", "end FirstOrder.Language\n", false)]
    [InlineData("section Local\nopen scoped FirstOrder\n", "end Local\n", false)]
    [InlineData("open scoped FirstOrder in\n", "", false)]
    [InlineData("open scoped FirstOrder in ", "", false)]
    [InlineData("open FirstOrder hiding Language\n", "", true)]
    public void EqualityContextFollowsCommandScopes(string prefix, string suffix, bool remainsActive)
    {
        foreach (var embedded in new[] { false, true })
        {
            var source = prefix + "theorem a : (t ='g') = (t =' g') := by rfl\n" + suffix
                + "theorem b : 'g' = 'g' := by rfl\n";
            var tokens = Scan(source, embedded);
            Assert.Equal(2, tokens.Count(token => token.Text == "='"));
            Assert.Equal(2, tokens.Count(token => token.IsIdentifier && token.Identifier == "g'"));
            // The next declaration probes restoration with the colliding compact spelling.
            var tail = Scan(source + (remainsActive ? "example : (t ='g') = (t =' g') := by rfl\n"
                : "example : 'g' ='g' := by rfl\n"), embedded);
            Assert.Equal(remainsActive ? 4 : 2, tail.Count(token => token.Text == "='"));
            Assert.Equal(remainsActive ? 4 : 2,
                LeanSourceCatalog.QualifiedIdentifiers(tail).Count(name => name == "g'"));
        }
    }

    [Theory]
    [InlineData("import Mathlib.ModelTheory.Syntax\n", "")]
    [InlineData("section FirstOrder\n", "end FirstOrder\n")]
    [InlineData("namespace Outer.FirstOrder\n", "end Outer.FirstOrder\n")]
    [InlineData("open FirstOrder (Language)\n", "")]
    [InlineData("open FirstOrder.Language\n", "")]
    [InlineData("open FirstOrder hiding Language in\n", "")]
    [InlineData("-- open scoped FirstOrder\n", "")]
    [InlineData("/- open scoped FirstOrder -/\n", "")]
    [InlineData("def text := \"open scoped FirstOrder\"\n", "")]
    public void EqualityContextDoesNotActivateFromUnrelatedOrInertText(string prefix, string suffix)
    {
        foreach (var embedded in new[] { false, true })
        {
            var tokens = Scan(prefix + "theorem a : 'g' ='g' := by rfl\n" + suffix, embedded);
            Assert.Equal(2, tokens.Count(token => token.Text == "'g'"));
            Assert.DoesNotContain("g'", LeanSourceCatalog.QualifiedIdentifiers(tokens));
        }
    }

    [Theory]
    [InlineData("\\q")]
    [InlineData("\\a")]
    [InlineData("\\b")]
    [InlineData("\\f")]
    [InlineData("\\v")]
    [InlineData("\\0")]
    [InlineData("\\/")]
    [InlineData("\\x0z")]
    [InlineData("\\u00xz")]
    public void CharacterEscapeRejectsInvalidSequences(string escape)
    {
        foreach (var embedded in new[] { false, true })
        {
            var error = Assert.Throws<LeanSourceExtractionException>(() => Scan("\n'" + escape + "'", embedded));
            Assert.Equal(2, error.Line);
            Assert.Equal("Lean character escape is malformed.", error.Message);
        }
    }

    [Theory]
    [InlineData("\\\\")]
    [InlineData("\\\"")]
    [InlineData("\\'")]
    [InlineData("\\r")]
    [InlineData("\\n")]
    [InlineData("\\t")]
    [InlineData("\\x61")]
    [InlineData("\\u0061")]
    public void CharacterEscapeAcceptsPinnedSimpleAndHexSequences(string escape)
    {
        foreach (var embedded in new[] { false, true })
        {
            var literal = "'" + escape + "'";
            var tokens = Scan("=" + literal, embedded);
            Assert.Equal(new[] { "=", literal }, tokens.Select(static token => token.Text));
            Assert.Empty(LeanSourceCatalog.QualifiedIdentifiers(tokens));
        }
    }

    private static System.Collections.Immutable.ImmutableArray<LeanSourceToken> Scan(string source, bool embedded) =>
        embedded ? LeanSourceTokenizer.TokenizeIncludingInterpolationTerms(source, SyntheticSourceContext.Equality(source))
            : LeanSourceTokenizer.Tokenize(source, SyntheticSourceContext.Equality(source));

    [Theory]
    [InlineData("')'")]
    [InlineData("'\\''")]
    [InlineData("r#\"quotes \" native_decide )\"#")]
    [InlineData("r##\"quotes \"# native_decide /-\"##")]
    [InlineData("`native_decide")]
    [InlineData("``native_decide")]
    [InlineData("\u00abnative_decide\u00bb")]
    [InlineData("native_decide!")]
    [InlineData("native_decide?")]
    [InlineData("native_decide\u2127")]
    [InlineData("native_decide\U0001d49c")]
    public void LexicalAtomsDoNotLeakInteriorTokensOrDelimiters(string atom)
    {
        var token = Assert.Single(LeanSourceTokenizer.Tokenize(atom));
        Assert.Equal(atom, token.Text);
    }

    [Theory]
    [InlineData("\u03bb")]
    [InlineData("\u03a0")]
    [InlineData("\u03a3")]
    public void LeanBinderSymbolsAreNotIdentifierSuffixes(string symbol)
    {
        Assert.Equal(new[] { "native_decide", symbol },
            LeanSourceTokenizer.Tokenize("native_decide" + symbol).Select(static token => token.Text));
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    [InlineData("\u2297'")]
    public void SymbolicPrimesDoNotConsumeFollowingCode(string symbol)
    {
        var tokens = LeanSourceTokenizer.Tokenize(symbol + " n, n\nnative_decide");
        Assert.Equal("native_decide", tokens[^1].Text);
        Assert.Equal(2, tokens[^1].Line);
    }

    [Fact]
    public void ImageNotationRetainsDoubleApostropheTokensAndLocations()
    {
        var tokens = LeanSourceTokenizer.Tokenize("f '' s\nnative_decide");
        Assert.Equal(new[] { "f", "''", "s", "native_decide" }, tokens.Select(static token => token.Text));
        Assert.False(tokens[1].IsIdentifier);
        Assert.Equal(1, tokens[1].Line);
        Assert.Equal(2, tokens[1].Column);
        Assert.Equal(2, tokens[^1].Line);
    }

    [Theory]
    [InlineData("\u2211'")]
    [InlineData("\u220f'")]
    public void PrimedNotationPrecedesAdjacentCharacterLookahead(string notation)
    {
        var tokens = LeanSourceTokenizer.Tokenize(notation + "n', f n'");
        Assert.Equal(new[] { notation, "n'", ",", "f", "n'" }, tokens.Select(static token => token.Text));
        Assert.False(tokens[0].IsIdentifier);
        Assert.Equal("n'", tokens[1].Identifier);
        Assert.Equal(2, tokens[1].Column);
    }

    [Fact]
    public void RegisteredProductMapNotationPreservesAdjacentPrimedIdentifier()
    {
        var tokens = LeanSourceTokenizer.Tokenize("f \u2297'g'");
        Assert.Equal(new[] { "f", "\u2297'", "g'" }, tokens.Select(static token => token.Text));
        Assert.False(tokens[1].IsIdentifier);
        Assert.Equal("g'", tokens[2].Identifier);
        Assert.Equal(4, tokens[2].Column);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MalformedCharacterAfterUnicodeSymbolFailsClosedWithLine(bool includeInterpolationTerms)
    {
        const string source = "\n\u2260'a";
        var exception = Assert.Throws<LeanSourceExtractionException>(() => includeInterpolationTerms
            ? LeanSourceTokenizer.TokenizeIncludingInterpolationTerms(source)
            : LeanSourceTokenizer.Tokenize(source));
        Assert.Equal(2, exception.Line);
        Assert.Equal("Lean character literal is unterminated or malformed.", exception.Message);
    }

    [Fact]
    public void CharacterLiteralAfterUnicodeOperatorRetainsItsSpelling()
    {
        var tokens = LeanSourceTokenizer.Tokenize("')' \u2260'}'");
        Assert.Equal(new[] { "')'", "\u2260", "'}'" }, tokens.Select(static token => token.Text));
    }

    [Fact]
    public void CharacterLiteralAfterAssignmentRetainsItsSpelling()
    {
        var tokens = LeanSourceTokenizer.Tokenize(":=')'");
        Assert.Equal(new[] { ":=", "')'" }, tokens.Select(static token => token.Text));
    }

    [Fact]
    public void ExistingPropositionTokensAndLocationsRemainStable()
    {
        var tokens = LeanSourceTokenizer.Tokenize("/- outer /- nested -/ -/\r\n theorem p (n : Nat) : n = n := by rfl -- end\n");
        Assert.Equal(new[] { "theorem", "p", "(", "n", ":", "Nat", ")", ":", "n", "=", "n", ":=", "by", "rfl" }, tokens.Select(static token => token.Text));
        Assert.All(tokens, token => Assert.Equal(2, token.Line));
        Assert.Equal(1, tokens[0].Column);
    }

    [Theory]
    [InlineData("/- unterminated")]
    [InlineData("\"unterminated")]
    [InlineData("(]")]
    [InlineData("(")]
    [InlineData("'(")]
    [InlineData("'ab'")]
    [InlineData(":='a")]
    [InlineData("'\\u00xz'")]
    public void ExistingMalformedSourceValidationRemainsFailClosed(string source)
    {
        Assert.Throws<LeanSourceExtractionException>(() => LeanSourceTokenizer.Tokenize(source));
    }

    [Fact]
    public void OrdinaryStringSpellingIsPreservedForPropositionExtraction()
    {
        const string source = "\"literal \\\" native_decide /- )\"";
        Assert.Equal(source, Assert.Single(LeanSourceTokenizer.Tokenize(source)).Text);
    }

    [Theory]
    [InlineData("s!\"value {(Fin.mk 1 (by native_decide) : Fin 2)}\"")]
    [InlineData("s!\"outer {s!\"inner {(Fin.mk 1 (by native_decide) : Fin 2)}\"}\"")]
    public void PropositionExtractionRetainsInterpolationLiteralWithoutExtraTermTokens(string source)
    {
        var tokens = LeanSourceTokenizer.Tokenize(source);
        Assert.Equal(new[] { "s!", source[2..] }, tokens.Select(static token => token.Text));
    }
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void Repair7IndentedOpenRetainsWholeIdentifierAndLocation(bool embedded, bool indented)
    {
        var source = "import Mathlib.ModelTheory.Syntax\n"
            + (indented ? " " : "") + "open scoped FirstOrder\n"
            + "example (t g'native_decide : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0))) :\n"
            + "    (t ='g'native_decide) = (t ='g'native_decide) := by rfl\n";
        var tokens = Scan(source, embedded);
        Assert.DoesNotContain(tokens, token => token.Text == "native_decide");
        var references = tokens.Where(token => token.Line == 4 && token.Identifier == "g'native_decide").ToArray();
        Assert.Equal(2, references.Length);
        Assert.Equal(9, references[0].Column);
        Assert.Equal(33, references[1].Column);
        Assert.Equal(3, LeanSourceCatalog.QualifiedIdentifiers(tokens).Count(name => name == "g'native_decide"));
    }

    [Theory]
    [InlineData(false, "FirstOrder")]
    [InlineData(true, "FirstOrder")]
    [InlineData(false, "Ordinary")]
    [InlineData(true, "Ordinary")]
    public void Repair7InitOnlyScopeKeepsCharactersInert(bool embedded, string ns)
    {
        var source = $"import Init\nnamespace {ns}\ndef g' : Nat := 0\nend {ns}\nopen {ns}\n"
            + "theorem a : 'g' ='g' := by rfl\n";
        var tokens = Scan(source, embedded).Where(token => token.Line == 6).ToArray();
        Assert.Equal(2, tokens.Count(token => token.Text == "'g'" && !token.IsIdentifier));
        Assert.DoesNotContain(tokens, token => token.IsIdentifier && token.Identifier == "g'");
        Assert.DoesNotContain("g'", LeanSourceCatalog.QualifiedIdentifiers([..tokens]));
    }

}
