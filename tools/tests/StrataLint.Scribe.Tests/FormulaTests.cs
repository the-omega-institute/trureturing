using System.Collections.Immutable;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Tests;

public sealed class FormulaTests
{
    [Fact]
    public void FormulaHasNoRawStringConstructionEntryPoint()
    {
        var rawEntrypoints = typeof(Formula).Assembly.GetTypes()
            .SelectMany(static type => type.GetMethods(
                System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.NonPublic
                | System.Reflection.BindingFlags.Static))
            .Where(static method => typeof(Formula).IsAssignableFrom(method.ReturnType))
            .Where(static method => method.GetParameters() is [{ ParameterType: var type }]
                && type == typeof(string))
            .Select(static method => $"{method.DeclaringType!.FullName}.{method.Name}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
        [
            "StrataLint.Scribe.DefinitionDsl.Id",
            "StrataLint.Scribe.FormulaDsl.Id",
        ],
            rawEntrypoints);
    }

    [Fact]
    public void LinearFormulaTokenVocabularyIsNotPubliclyReachable()
    {
        var assembly = typeof(Formula).Assembly;
        var forbiddenTypes = new[]
        {
            "StrataLint.Scribe.FormulaToken",
            "StrataLint.Scribe.FormulaMark",
            "StrataLint.Scribe.FormulaSpace",
            "StrataLint.Scribe.Formula+TokenTree",
        };

        foreach (var typeName in forbiddenTypes)
        {
            Assert.Null(assembly.GetType(typeName, throwOnError: false));
        }

        var forbiddenFactories = new[] { "FormulaTokens", "W", "M", "K", "S", "P" };
        var exposedFactories = typeof(DefinitionDsl).GetMethods(
                System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.Static)
            .Select(static method => method.Name)
            .Intersect(forbiddenFactories, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(exposedFactories);
    }

    [Fact]
    public void StructuralPresentationPreservesDelimitersAndAlignedRows()
    {
        Formula inline = new Formula.Layout(
            FormulaLayoutMode.Inline,
            Equal(Call("realPart", Id("s")), new Formula.Fraction(Num(1), Num(2))));
        Formula display = new Formula.Layout(
            FormulaLayoutMode.Display,
            new Formula.Aligned([
                Equal(Id("x"), Num(1)),
                Equal(Id("y"), Num(2)),
            ]));

        Assert.Equal(@"$\operatorname{realPart}\left(s\right) = \frac{1}{2}$", LatexWriter.WriteStatement(inline));
        Assert.Equal(@"$$\begin{aligned}x = 1\\y = 2\end{aligned}$$", LatexWriter.WriteStatement(display));
        Assert.IsType<Formula.Layout>(inline);
        Assert.IsType<Formula.Aligned>(((Formula.Layout)display).Content);
    }

    [Fact]
    public void IdentifierRejectsSyntaxThatHasDedicatedAstNodes()
    {
        Assert.Throws<ArgumentException>(() => FormulaIdentifier.Create("phi_1"));
    }

    [Fact]
    public void LatexWriterEmitsEmbeddingAndLogGrammarCanonically()
    {
        Formula goldenIdentity = new Formula.Relation(
            new Formula.Power(new Formula.Phi(), Num(2)),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                new Formula.Phi(),
                FormulaBinaryOperator.Add,
                Num(1)));
        Formula logarithmicScale = new Formula.Floor(
            new Formula.Log(
                new Formula.Phi(),
                new Formula.Absolute(
                    new Formula.FunctionCall(
                        FormulaIdentifier.Create("embedding"),
                        [Id("x")]))));

        Assert.Equal("\\varphi^{2} = \\varphi + 1", LatexWriter.Write(goldenIdentity));
        Assert.Equal(
            "\\left\\lfloor\\log_{\\varphi}\\left(\\left|\\operatorname{embedding}\\left(x\\right)\\right|\\right)\\right\\rfloor",
            LatexWriter.Write(logarithmicScale));
    }

    [Fact]
    public void LatexWriterEmitsSubscriptsFractionsAndPsiCanonically()
    {
        Formula indexedPower = new Formula.Power(
            new Formula.Subscript(Id("x"), Id("n")),
            Num(2));
        Formula half = new Formula.Fraction(Num(1), Num(2));
        Formula conjugateIdentity = new Formula.Relation(
            new Formula.Psi(),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                Num(1),
                FormulaBinaryOperator.Subtract,
                new Formula.Phi()));

        Assert.Equal("\\left(x_{n}\\right)^{2}", LatexWriter.Write(indexedPower));
        Assert.Equal("\\frac{1}{2}", LatexWriter.Write(half));
        Assert.Equal("\\psi = 1 - \\varphi", LatexWriter.Write(conjugateIdentity));
    }

    [Fact]
    public void LatexWriterEmitsModuloSequenceAndSetNotationCanonically()
    {
        Formula phase = new Formula.Modulo(
            new Formula.Binary(Id("n"), FormulaBinaryOperator.Multiply, new Formula.Phi()),
            Num(1));
        Formula sequence = new Formula.Sequence(phase, Id("n"), new Formula.Integers());
        Formula orbit = new Formula.SetBuilder(phase, Id("n"), new Formula.Integers());
        Formula constants = new Formula.SetLiteral(
            ImmutableArray.Create<Formula>(new Formula.Phi(), new Formula.Psi()));

        Assert.Equal(
            "\\left(n \\cdot \\varphi \\bmod 1\\right)_{n \\in \\mathbb{Z}}",
            LatexWriter.Write(sequence));
        Assert.Equal(
            "\\left\\{n \\cdot \\varphi \\bmod 1 \\mid n \\in \\mathbb{Z}\\right\\}",
            LatexWriter.Write(orbit));
        Assert.Equal("\\left\\{\\varphi, \\psi\\right\\}", LatexWriter.Write(constants));
    }

    [Fact]
    public void LatexWriterEmitsIdenticalUtf8BytesOnEveryRun()
    {
        Formula formula = new Formula.Fraction(
            new Formula.Binary(Id("a"), FormulaBinaryOperator.Add, Id("b")),
            Id("c"));

        var first = LatexWriter.WriteUtf8(formula);
        var second = LatexWriter.WriteUtf8(formula);

        Assert.Equal(first.ToArray(), second.ToArray());
        Assert.Equal("\\frac{a + b}{c}", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsTheOptionMapSectionPlaceholderCanonically()
    {
        Formula formula = new Formula.FunctionCall(
            FormulaIdentifier.Create("map"),
            [
                new Formula.Binary(
                    Id("n"),
                    FormulaBinaryOperator.Add,
                    new Formula.Placeholder()),
                new Formula.FunctionCall(
                    FormulaIdentifier.Create("logScale"),
                    [Id("x")]),
            ]);

        Assert.Equal(
            "\\operatorname{map}\\left(n + \\mathord{\\cdot}, \\operatorname{logScale}\\left(x\\right)\\right)",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void RelationChainEmitsConstructivelyWithoutParsingLatex()
    {
        Formula formula = new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [
                new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [Num(89)]),
                new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [Num(123)]),
                new Formula.Subscript(Num(1010000000), Id("W")),
            ]);

        Assert.Equal(
            "\\operatorname{Z}\\left(89\\right) = \\operatorname{Z}\\left(123\\right) = 1010000000_{W}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterParenthesizesRepeatedScriptBases()
    {
        Formula nestedPower = new Formula.Power(
            new Formula.Power(Id("x"), Num(2)),
            Num(3));
        Formula nestedSubscript = new Formula.Subscript(
            new Formula.Subscript(Id("x"), Id("n")),
            Id("m"));

        Assert.Equal("\\left(x^{2}\\right)^{3}", LatexWriter.Write(nestedPower));
        Assert.Equal("\\left(x_{n}\\right)_{m}", LatexWriter.Write(nestedSubscript));
    }

    [Fact]
    public void LatexWriterPreservesMultiplicationByANegatedOperand()
    {
        Formula formula = new Formula.Binary(
            Id("x"),
            FormulaBinaryOperator.Multiply,
            new Formula.Negate(Num(1)));

        Assert.Equal("x \\cdot \\left(-1\\right)", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsANestedRightFactorThatStartsWithNegation()
    {
        Formula formula = new Formula.Binary(
            Id("x"),
            FormulaBinaryOperator.Multiply,
            new Formula.Binary(
                new Formula.Negate(Num(1)),
                FormulaBinaryOperator.Multiply,
                Id("y")));

        Assert.Equal("x \\cdot \\left(-1 \\cdot y\\right)", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsASequenceBeforeApplyingAnotherSubscript()
    {
        Formula formula = new Formula.Subscript(
            new Formula.Sequence(Id("x"), Id("n"), new Formula.Integers()),
            Id("m"));

        Assert.Equal(
            "\\left(\\left(x\\right)_{n \\in \\mathbb{Z}}\\right)_{m}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsAnExplicitOperatorForNumericMultiplication()
    {
        Formula formula = new Formula.Binary(
            Num(1),
            FormulaBinaryOperator.Multiply,
            Num(2));

        Assert.Equal("1 \\cdot 2", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsCrossedScriptChains()
    {
        Formula formula = new Formula.Power(
            new Formula.Subscript(
                new Formula.Power(Id("x"), Num(2)),
                Id("n")),
            Num(3));

        Assert.Equal(
            "\\left(\\left(x^{2}\\right)_{n}\\right)^{3}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void NegativeNumbersUseTheDedicatedNegateNode()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new Formula.Number(-1));
    }

    [Fact]
    public void LatexWriterIsTotalAndDeterministicForTheClosedFormulaVocabulary()
    {
        var identifier = FormulaIdentifier.Create("f");
        var x = Id("x");
        var formulas = new Formula[]
        {
            new Formula.Symbol(identifier),
            Num(1),
            new Formula.Phi(),
            new Formula.Psi(),
            new Formula.Placeholder(),
            new Formula.Integers(),
            new Formula.Negate(x),
            new Formula.Absolute(x),
            new Formula.Binary(x, FormulaBinaryOperator.Add, Num(1)),
            new Formula.Fraction(x, Num(2)),
            new Formula.Subscript(x, Num(1)),
            new Formula.Power(x, Num(2)),
            new Formula.Floor(x),
            new Formula.Log(Num(2), x),
            new Formula.Modulo(x, Num(2)),
            new Formula.Sequence(x, Id("n"), new Formula.Integers()),
            new Formula.SetLiteral([x]),
            new Formula.SetBuilder(x, Id("n"), new Formula.Integers()),
            new Formula.FunctionCall(identifier, [x]),
            new Formula.Relation(x, FormulaRelationOperator.NotEqual, Num(0)),
            new Formula.RelationChain(FormulaRelationOperator.Equal, [x, Num(1)]),
        };

        foreach (var formula in formulas)
        {
            var first = LatexWriter.Write(formula);
            var second = LatexWriter.Write(formula);
            Assert.NotEmpty(first);
            Assert.Equal(first, second);
        }
    }

    [Fact]
    public void FormulaConstructorsRejectMissingChildrenAndDefaultCollections()
    {
        Assert.Throws<ArgumentNullException>(() => new Formula.Negate(null!));
        Assert.Throws<ArgumentNullException>(() => new Formula.Binary(
            null!,
            FormulaBinaryOperator.Add,
            Num(1)));
        Assert.Throws<ArgumentNullException>(() => new Formula.Relation(
            Num(1),
            FormulaRelationOperator.Equal,
            null!));
        Assert.Throws<ArgumentException>(() => new Formula.SetLiteral(default));
        Assert.Throws<ArgumentException>(() => new Formula.FunctionCall(
            FormulaIdentifier.Create("f"),
            default));
        Assert.Throws<ArgumentException>(() => new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [Num(1)]));
        Assert.Throws<ArgumentException>(() => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [],
            new Formula.Relation(Id("x"), FormulaRelationOperator.Equal, Id("x"))));
        Assert.Throws<ArgumentException>(() => new Formula.Aligned([]));
    }

    [Fact]
    public void LatexWriterParenthesizesBindManyNestedInLogicConjunction()
    {
        Formula formula = new Formula.Logic(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [
                    new Formula.BoundVariable(FormulaIdentifier.Create("x"), new Formula.Integers()),
                    new Formula.BoundVariable(FormulaIdentifier.Create("y"), new Formula.Integers()),
                ],
                Id("P")),
            FormulaLogicOperator.And,
            Id("Q"));

        Assert.Equal(
            "\\left(\\forall x \\in \\mathbb{Z}, y \\in \\mathbb{Z},\\; P\\right) \\land Q",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsTheInventoriedLogicalCoreCanonically()
    {
        Formula formula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Integers")),
            new Formula.Logic(
                new Formula.Relation(Id("x"), FormulaRelationOperator.GreaterThanOrEqual, Num(0)),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    new Formula.Norm(Id("x")),
                    FormulaRelationOperator.MemberOf,
                    new Formula.NamedConstant(FormulaIdentifier.Create("Naturals")))));

        Assert.Equal(
            "\\forall x \\in \\mathrm{Integers},\\; x \\ge 0 \\Rightarrow \\left\\lVert x \\right\\rVert \\in \\mathrm{Naturals}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsApplyTypeArrowAndBiconditional()
    {
        Formula functionType = new Formula.TypeArrow(
            new Formula.NamedConstant(FormulaIdentifier.Create("Real")),
            new Formula.NamedConstant(FormulaIdentifier.Create("Complex")));
        Formula application = new Formula.Apply(
            new Formula.NamedConstant(FormulaIdentifier.Create("embedding")),
            [Id("x")]);
        Formula formula = new Formula.Logic(
            new Formula.Relation(application, FormulaRelationOperator.Equivalent, Id("x")),
            FormulaLogicOperator.Iff,
            new Formula.Relation(functionType, FormulaRelationOperator.NotEqual, Id("x")));

        Assert.Equal(
            "\\mathrm{embedding}\\left(x\\right) \\equiv x \\Leftrightarrow \\left(\\mathrm{Real} \\to \\mathrm{Complex}\\right) \\ne x",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void NewClosedOperatorsRejectUndefinedEnumValues()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new Formula.Bind(
            (FormulaQuantifier)99,
            FormulaIdentifier.Create("x"),
            new Formula.Integers(),
            new Formula.Relation(Id("x"), FormulaRelationOperator.Equal, Id("x"))));
        Assert.Throws<ArgumentOutOfRangeException>(() => new Formula.Logic(
            new Formula.Relation(Id("x"), FormulaRelationOperator.Equal, Id("x")),
            (FormulaLogicOperator)99,
            new Formula.Relation(Id("x"), FormulaRelationOperator.Equal, Id("x"))));
        Assert.Throws<ArgumentOutOfRangeException>(() => new Formula.Relation(
            Id("x"),
            (FormulaRelationOperator)99,
            Id("x")));
    }

    [Fact]
    public void ScriptSymbolRejectsAMultiTokenArgument()
    {
        // `^` takes exactly one token, so `^\operatorname{card}(A)` leaves \operatorname
        // without its argument and KaTeX refuses the whole formula.
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
        [
            FormulaDsl.Id("x"),
            FormulaDsl.Caret,
            FormulaDsl.Seq(
                FormulaDsl.Operatorname,
                FormulaDsl.Grp(FormulaDsl.Id("card")),
                FormulaDsl.Open,
                FormulaDsl.Id("A"),
                FormulaDsl.Close),
        ]));

        // The same defect inside a group is the same defect.
        Assert.Throws<ArgumentException>(() => new Formula.LatexGroup(
        [
            FormulaDsl.Id("x"),
            FormulaDsl.Underscore,
            FormulaDsl.Seq(FormulaDsl.Id("a"), FormulaDsl.Id("b")),
        ]));
    }

    [Fact]
    public void ScriptSymbolRejectsAMultiCharacterOrDanglingArgument()
    {
        // `_alpha` renders as `_{a}lpha`: KaTeX accepts it and the reader is silently misled.
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
            [FormulaDsl.Id("I"), FormulaDsl.Underscore, FormulaDsl.Id("alpha")]));
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
            [FormulaDsl.Id("x"), FormulaDsl.Caret, FormulaDsl.D(1, 2)]));

        // A script with nothing to attach to, and a script attached to another script.
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
            [FormulaDsl.Id("x"), FormulaDsl.Caret]));
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
            [FormulaDsl.Id("x"), FormulaDsl.Caret, FormulaDsl.Underscore, FormulaDsl.Id("a")]));
    }

    [Fact]
    public void ScriptSymbolAcceptsASingleTokenArgument()
    {
        var accepted = new[]
        {
            FormulaDsl.Grp(FormulaDsl.Operatorname, FormulaDsl.Grp(FormulaDsl.Id("card"))),
            FormulaDsl.Id("a"),
            FormulaDsl.D(2),
            FormulaDsl.Minus,
            FormulaDsl.Alpha,
            FormulaDsl.Perp,
            FormulaDsl.Frac,
            new Formula.Number(7),
            new Formula.Phi(),
            new Formula.Integers(),
        };

        foreach (var argument in accepted)
        {
            _ = new Formula.LatexSequence([FormulaDsl.Id("x"), FormulaDsl.Caret, argument]);
            _ = new Formula.LatexSequence([FormulaDsl.Id("x"), FormulaDsl.Underscore, argument]);
        }

        // TeX skips whitespace between the script mark and its single-token argument.
        _ = new Formula.LatexSequence(
            [FormulaDsl.Id("x"), FormulaDsl.Caret, FormulaDsl.Sp, FormulaDsl.Grp(FormulaDsl.Id("a"))]);
    }

    [Fact]
    public void ScriptChainsAreRefusedWhereTheBaseAlreadyCarriesTheScript()
    {
        // `T^{*}^{k}` is a KaTeX parse error ("Double superscript"): TeX binds one script
        // mark per base. The scripted base is a nested sequence, so only its tail shows it.
        var superscripted = FormulaDsl.Seq(
            FormulaDsl.Id("T"), FormulaDsl.Caret, FormulaDsl.Grp(FormulaDsl.Star));
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
            [superscripted, FormulaDsl.Caret, FormulaDsl.Grp(FormulaDsl.Id("k"))]));

        // `u_{n}_{i}` is the same defect one script mark down, and a group is no shelter.
        Assert.Throws<ArgumentException>(() => new Formula.LatexGroup(
        [
            FormulaDsl.Seq(FormulaDsl.Id("u"), FormulaDsl.Underscore, FormulaDsl.Grp(FormulaDsl.Id("n"))),
            FormulaDsl.Underscore,
            FormulaDsl.Grp(FormulaDsl.Id("i")),
        ]));

        // A structured script over the same tail is the same chain.
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
        [
            new Formula.Power(FormulaDsl.Id("x"), FormulaDsl.D(2)),
            FormulaDsl.Caret,
            FormulaDsl.Grp(FormulaDsl.D(3)),
        ]));

        // Grouping the base states the nesting, and is what the rejection asks for.
        Assert.Equal(
            "{T^{*}}^{k}",
            LatexWriter.Write(FormulaDsl.Seq(
                FormulaDsl.Grp(FormulaDsl.Id("T"), FormulaDsl.Caret, FormulaDsl.Grp(FormulaDsl.Star)),
                FormulaDsl.Caret,
                FormulaDsl.Grp(FormulaDsl.Id("k")))));

        // One base carries one of each, so a superscript after a subscript is no chain.
        Assert.Equal(
            "\\sum_{n=0}^{\\infty}",
            LatexWriter.Write(FormulaDsl.Seq(
                FormulaDsl.Sum,
                FormulaDsl.Underscore,
                FormulaDsl.Grp(FormulaDsl.Id("n"), FormulaDsl.Eq, FormulaDsl.D(0)),
                FormulaDsl.Caret,
                FormulaDsl.Grp(FormulaDsl.Infty))));

        // An empty group opens a fresh base, which is how TeX itself stacks two scripts.
        Assert.Equal(
            "T^{*}{}^{k}",
            LatexWriter.Write(FormulaDsl.Seq(
                superscripted,
                FormulaDsl.Grp(),
                FormulaDsl.Caret,
                FormulaDsl.Grp(FormulaDsl.Id("k")))));
    }

    [Fact]
    public void EmissionRefusesAScriptChainAssembledAcrossNodes()
    {
        // A structured script parenthesizes a structured scripted base, but it cannot see
        // the tail of a raw sequence, so the chain only exists in the finished bytes.
        var chained = new Formula.Power(
            FormulaDsl.Seq(FormulaDsl.Id("T"), FormulaDsl.Caret, FormulaDsl.Grp(FormulaDsl.Star)),
            FormulaDsl.Id("k"));

        var rejection = Assert.Throws<InvalidOperationException>(() => LatexWriter.Write(chained));

        Assert.Contains("already carries a '^' script", rejection.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MacrosAreRefusedWhereTheirArgumentIsMissing()
    {
        // `\operatorname\left({NeZero}, d\right)` applies the macro before it has its
        // own argument, so `\left` lands in the argument position and KaTeX refuses the
        // formula with "Expected group as argument to '\operatorname'".
        Assert.Throws<ArgumentException>(() => new Formula.Apply(
            FormulaDsl.Operatorname,
            [FormulaDsl.Grp(FormulaDsl.Id("NeZero")), FormulaDsl.Id("d")]));

        // The same defect spelled as a sequence, and left dangling at the end of one.
        Assert.Throws<ArgumentException>(() => new Formula.LatexSequence(
        [
            FormulaDsl.Operatorname,
            FormulaDsl.Left,
            FormulaDsl.Open,
            FormulaDsl.Id("d"),
            FormulaDsl.Right,
            FormulaDsl.Close,
        ]));
        Assert.Throws<ArgumentException>(() => new Formula.LatexGroup(
            [FormulaDsl.Id("x"), FormulaDsl.Mathbb]));

        // Naming the operator first is the fix.
        Assert.Equal(
            "\\operatorname{NeZero}\\left(d\\right)",
            LatexWriter.Write(new Formula.Apply(
                FormulaDsl.Seq(FormulaDsl.Operatorname, FormulaDsl.Grp(FormulaDsl.Id("NeZero"))),
                [FormulaDsl.Id("d")])));

        // TeX discards the whitespace between a macro and its argument, and `\frac` binds
        // two tokens, so a digit pair legally serves both.
        Assert.Equal(
            "\\operatorname {Inv}",
            LatexWriter.Write(FormulaDsl.Seq(
                FormulaDsl.Operatorname, FormulaDsl.Sp, FormulaDsl.Grp(FormulaDsl.Id("Inv")))));
        Assert.Equal(
            "\\frac12",
            LatexWriter.Write(FormulaDsl.Seq(FormulaDsl.Frac, FormulaDsl.D(1, 2))));
    }

    [Fact]
    public void MacrosRefusedAsAScriptArgumentAreExactlyTheMeasuredKatexSet()
    {
        // Measured against katex 0.16 by rendering `x^<macro><minimal legal argument>`:
        // every member below raises "Got function ... with no arguments as superscript",
        // and every non-member renders. Grouping the argument fixes all of them. The
        // trailing group is that minimal argument: it keeps the macros that bind one from
        // being refused for the unrelated reason of standing bare.
        string[] refused =
        [
            "Begin", "End", "Exp", "Gcd", "Iff", "Implies", "Ker", "Left", "Lim", "Log",
            "Max", "Middle", "Min", "NegativeThinSpace", "Operatorname", "Overline", "Prod",
            "Qquad", "Quad", "Right", "RowBreak", "SemicolonSpace", "Sin", "Sqrt", "Sum",
            "ThinSpace", "Widehat", "Widetilde",
        ];

        var observed = new List<string>();
        foreach (var macro in Enum.GetValues<FormulaLatexMacro>())
        {
            try
            {
                _ = new Formula.LatexSequence(
                [
                    FormulaDsl.Id("x"),
                    FormulaDsl.Caret,
                    new Formula.LatexMacro(macro),
                    FormulaDsl.Grp(FormulaDsl.Id("a")),
                ]);
            }
            catch (ArgumentException)
            {
                observed.Add(macro.ToString());
            }
        }

        Assert.Equal(refused.Order(StringComparer.Ordinal), observed.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void EverySymbolAndMacroIsExplicitlyClassifiedAsAScriptArgument()
    {
        // No enum member may fall through to a default: a new macro must state its class.
        foreach (var macro in Enum.GetValues<FormulaLatexMacro>())
        {
            var caught = Record.Exception(() => new Formula.LatexSequence(
                [FormulaDsl.Id("x"), FormulaDsl.Caret, new Formula.LatexMacro(macro)]));
            Assert.True(
                caught is null or ArgumentException,
                $"{macro} is unclassified: {caught?.GetType().Name}");
        }

        string[] refusedSymbols = ["Ampersand", "Apostrophe", "Caret", "Underscore"];
        var observed = new List<string>();
        foreach (var symbol in Enum.GetValues<FormulaLatexSymbol>())
        {
            var caught = Record.Exception(() => new Formula.LatexSequence(
                [FormulaDsl.Id("x"), FormulaDsl.Caret, new Formula.LatexSymbol(symbol)]));
            Assert.True(
                caught is null or ArgumentException,
                $"{symbol} is unclassified: {caught?.GetType().Name}");
            if (caught is not null) observed.Add(symbol.ToString());
        }

        Assert.Equal(refusedSymbols.Order(StringComparer.Ordinal), observed.Order(StringComparer.Ordinal));
    }

    private static Formula Id(string value) =>
        new Formula.Symbol(FormulaIdentifier.Create(value));

    private static Formula Num(long value) => new Formula.Number(value);
}
