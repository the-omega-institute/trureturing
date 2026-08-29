using System.Buffers.Binary;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed partial class FormulaCorpusInventoryTests
{
    private const string CanonicalRendererSha256 =
        "f79f527e59e01d4938e86f31ec4a4cc6410c06caef222873adf3cf29635c30a1";
    private const string UpdateCommand = "make -C tools update-renderer-contract";

    [Fact]
    public void RendererVocabularyPreservesRenderingCombinations()
    {
        var x = new Formula.Symbol(FormulaIdentifier.Create("x"));
        var y = new Formula.Symbol(FormulaIdentifier.Create("y"));
        var vocabulary = RendererVocabulary(
            FixedDocumentCorpus(),
            [new Formula.Power(new Formula.Power(x, y), new Formula.Number(2))]);

        Assert.Contains(
            "describe:kind=Theorem;provenance=RepoDerived;statement=LeanDeclaration",
            vocabulary);
        Assert.Contains(
            "formula-context:Power.Base=precedence:script;produces-script:true;starts-with-negation:false",
            vocabulary);
        Assert.Contains(
            "formula-context:Power.Exponent=precedence:atom;produces-script:false;starts-with-negation:false",
            vocabulary);
        Assert.Contains(
            "formula-children:Power(Base=Power,Exponent=Number)",
            vocabulary);
    }

    [Fact]
    public void FixedSyntheticCorpusFreezesRendererBehavior()
    {
        var fixedFormulas = FixedFormulaCorpus();
        var fixedDocuments = FixedDocumentCorpus();
        var fixedReport = LeanReportFixture.ForDocuments(fixedDocuments);
        var fixedCatalog = DeclarationCatalog.Create(fixedReport);
        var fixedGraph = DocumentGraphAssembler.Assemble(fixedDocuments, fixedCatalog);
        Assert.Empty(fixedGraph.Findings);

        using var aggregate = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var formula in fixedFormulas)
        {
            AppendLengthPrefixed(aggregate, Encoding.UTF8.GetBytes(FormulaKey(formula)));
            AppendLengthPrefixed(aggregate, Encoding.UTF8.GetBytes(LatexWriter.Write(formula)));
        }

        var citations = new Dictionary<string, LiteratureCitation>(StringComparer.Ordinal)
        {
            ["sos1957threegap"] = LiteratureCitation.Create(
                "Synthetic Author",
                2026,
                "Renderer contract fixture",
                "10.1000/renderer-contract"),
        };
        foreach (var document in fixedDocuments.OrderBy(
                     static document => document.Header.Gid.Value,
                     StringComparer.Ordinal))
        {
            AppendLengthPrefixed(
                aggregate,
                Encoding.UTF8.GetBytes(document.Header.Gid.Value));
            AppendLengthPrefixed(
                aggregate,
                CanonicalMarkdownWriter.Write(
                    document,
                    fixedCatalog,
                    citations,
                    fixedGraph).ToArray());
        }

        var actual = Convert.ToHexString(aggregate.GetHashAndReset()).ToLowerInvariant();
        if (Environment.GetEnvironmentVariable("STRATALINT_PRINT_RENDERER_CONTRACT") == "1")
        {
            throw new Xunit.Sdk.XunitException(
                $"Renderer behavior contract print mode. expected={CanonicalRendererSha256}; "
                    + $"actual={actual}; update=`{UpdateCommand}`; "
                    + $"RENDERER_CONTRACT_SHA256={actual}");
        }

        Assert.True(
            string.Equals(CanonicalRendererSha256, actual, StringComparison.Ordinal),
            $"Renderer behavior contract changed. expected={CanonicalRendererSha256}; "
                + $"actual={actual}. If intentional, run `{UpdateCommand}`.");
    }

    private static void AssertRendererVocabularyCoverage(
        IReadOnlyCollection<DocumentDefinition> repositoryDefinitions)
    {
        var fixedVocabulary = RendererVocabulary(FixedDocumentCorpus(), FixedFormulaCorpus());
        var repositoryVocabulary = RendererVocabulary(
            repositoryDefinitions.Select(static definition => definition.Document),
            []);
        var uncovered = repositoryVocabulary
            .Except(fixedVocabulary, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.True(
            uncovered.Length == 0,
            "The fixed renderer corpus does not cover repository rendering combinations: "
                + string.Join(", ", uncovered));
        AssertClosedFormulaVocabularyIsCovered(fixedVocabulary);
    }

    private static IReadOnlyList<ScribeDocument> FixedDocumentCorpus()
    {
        var sourceGid = "D5/S0/Synthetic/RendererContract";
        var targetGid = "D5/S0/Synthetic/RendererTarget";
        var commentary = DefinitionDsl.Blocks(DefinitionDsl.Paragraph(
            DefinitionDsl.Text("Fixed commentary.")));
        var formula = FormulaDsl.Seq(FormulaDsl.Id("x"), FormulaDsl.Esc, FormulaDsl.Id("y"));

        var source = ScribeDocument.Create(
            Header(sourceGid, "Fixed renderer digest."),
            Heading.Create("Renderer contract"),
            BlockSequence.Create(
            [
                DefinitionDsl.Paragraph(
                    DefinitionDsl.Text("Text "),
                    DefinitionDsl.Math(new Formula.Phi()),
                    DefinitionDsl.Text(" and "),
                    DefinitionDsl.Ref(targetGid),
                    DefinitionDsl.Text(".")),
                new DocumentBlock.DisplayFormula(new Formula.Psi()),
                new DocumentBlock.Section(
                    Heading.Create("Kinds"),
                    BlockSequence.Create(
                    [
                        SyntheticLeanDescribe("definition", DescribeKind.Definition, commentary),
                        SyntheticLeanDescribe("theorem", DescribeKind.Theorem, commentary),
                        SyntheticLeanDescribe("proposition", DescribeKind.Proposition, commentary),
                        SyntheticLeanDescribe("lemma", DescribeKind.Lemma, commentary),
                        SyntheticLeanDescribe(
                            "literature-definition",
                            DescribeKind.Definition,
                            commentary,
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap"))),
                        SyntheticLeanDescribe(
                            "literature-theorem",
                            DescribeKind.Theorem,
                            commentary,
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap"))),
                        SyntheticLeanDescribe(
                            "literature-proposition",
                            DescribeKind.Proposition,
                            commentary,
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap"))),
                        SyntheticLeanDescribe(
                            "literature-lemma",
                            DescribeKind.Lemma,
                            commentary,
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap"))),
                        Describe.Example(
                            DescribeId.Create("example"),
                            Heading.Create("Example"),
                            formula,
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap")),
                            commentary),
                        Describe.Example(
                            DescribeId.Create("repo-example"),
                            Heading.Create("Repository example"),
                            formula,
                            AssessedProvenance.FromRepo(),
                            commentary),
                        Describe.Remark(
                            DescribeId.Create("novel-remark"),
                            Heading.Create("Novel remark"),
                            new Formula.Number(1),
                            AssessedProvenance.NovelAfterSearch(GidRef.Create(sourceGid)),
                            commentary),
                        Describe.Remark(
                            DescribeId.Create("lean-remark"),
                            DeclarationHandle.Create(sourceGid + ".remark"),
                            Heading.Create("Lean remark"),
                            AssessedProvenance.FromRepo(),
                            commentary),
                        Describe.Remark(
                            DescribeId.Create("literature-remark"),
                            DeclarationHandle.Create(sourceGid + ".literature_remark"),
                            Heading.Create("Literature remark"),
                            AssessedProvenance.FromLiterature(
                                LibraryNoteRef.Create("D5/L/sos1957threegap")),
                            commentary),
                    ])),
            ]),
            [
                DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create(sourceGid + ".lemma")),
                DocumentEdge.Dependency.Create(GidRef.Create(targetGid)),
                DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(targetGid)),
                DocumentEdge.NarrativeReference.ToDescribe(
                    GidRef.Create(targetGid),
                    DescribeId.Create("target")),
            ]);
        var target = ScribeDocument.Create(
            Header(targetGid, "Fixed target digest."),
            Heading.Create("Renderer target"),
            DefinitionDsl.Blocks(Describe.Remark(
                DescribeId.Create("target"),
                Heading.Create("Target"),
                new Formula.Number(2),
                AssessedProvenance.FromRepo(),
                commentary)));
        return [source, target];

        static DocumentBlock.Describe SyntheticLeanDescribe(
            string id,
            DescribeKind kind,
            BlockSequence commentary,
            AssessedProvenance? provenance = null)
        {
            var constructor = typeof(DocumentBlock.Describe)
                .GetConstructors(BindingFlags.Instance | BindingFlags.NonPublic)
                .Single(static candidate => candidate.GetParameters().Length == 9);
            var declaration = LeanDeclarationRef.Create(
                $"D5/S0/Synthetic/RendererContract.{id.Replace('-', '_')}");
            return (DocumentBlock.Describe)constructor.Invoke(
            [
                DescribeId.Create(id),
                kind,
                Heading.Create(char.ToUpperInvariant(id[0]) + id[1..]),
                DescribeStatement.FromLean(declaration),
                provenance ?? AssessedProvenance.FromRepo(),
                commentary,
                null,
                null,
                null,
            ]);
        }
    }

    private static DocumentHeader Header(string gid, string digest) => DocumentHeader.Create(
        GidRef.Create(gid),
        Generality.Instance,
        GidRef.Create("D5/B/" + gid["D5/".Length..]),
        new EvidenceMirror.Waiver(WaiverReason.Create("renderer-contract")),
        [],
        Digest.Create(digest));

    private static IReadOnlyList<Formula> FixedFormulaCorpus()
    {
        var x = new Formula.Symbol(FormulaIdentifier.Create("x"));
        var y = new Formula.Symbol(FormulaIdentifier.Create("y"));
        var one = new Formula.Number(1);
        var formulas = new List<Formula>
        {
            new Formula.Aligned([x, y]),
            new Formula.LatexSequence([FormulaDsl.Id("x"), FormulaDsl.Esc, FormulaDsl.Id("y")]),
            new Formula.LatexGroup([x, y]),
            new Formula.LatexSpace(),
            new Formula.LatexNewline(),
            new Formula.LatexWord(FormulaIdentifier.Create("word")),
            new Formula.LatexDigits([1, 2]),
            new Formula.Layout(FormulaLayoutMode.Inline, x),
            new Formula.Layout(FormulaLayoutMode.Display, x),
            x,
            one,
            new Formula.Phi(),
            new Formula.Psi(),
            new Formula.Placeholder(),
            new Formula.Integers(),
            new Formula.NamedConstant(FormulaIdentifier.Create("Fixed")),
            new Formula.Negate(x),
            new Formula.Absolute(x),
            new Formula.Norm(x),
            new Formula.Fraction(x, one),
            new Formula.Subscript(x, one),
            new Formula.Power(x, one),
            new Formula.Floor(x),
            new Formula.Floor(new Formula.Binary(x, FormulaBinaryOperator.Multiply, y)),
            new Formula.Log(one, x),
            new Formula.Modulo(x, one),
            new Formula.Sequence(x, y, new Formula.Integers()),
            new Formula.SetLiteral([]),
            new Formula.SetLiteral([x, y]),
            new Formula.SetBuilder(x, y, new Formula.Integers()),
            new Formula.FunctionCall(FormulaIdentifier.Create("f"), [x, y]),
            new Formula.Apply(x, [x, y]),
            new Formula.TypeArrow(x, y),
            new Formula.Not(x),
        };
        formulas.AddRange(Enum.GetValues<FormulaLatexMacro>()
            .Select(static value => (Formula)new Formula.LatexMacro(value)));
        formulas.AddRange(Enum.GetValues<FormulaLatexSymbol>()
            .Select(static value => (Formula)new Formula.LatexSymbol(value)));
        formulas.AddRange(Enum.GetValues<FormulaBinaryOperator>()
            .Select(value => (Formula)new Formula.Binary(x, value, y)));
        formulas.AddRange(Enum.GetValues<FormulaRelationOperator>()
            .SelectMany(value => new Formula[]
            {
                new Formula.Relation(x, value, y),
                new Formula.RelationChain(value, [x, one, y]),
            }));
        formulas.AddRange(Enum.GetValues<FormulaLogicOperator>()
            .Select(value => (Formula)new Formula.Logic(x, value, y)));
        formulas.AddRange(Enum.GetValues<FormulaQuantifier>()
            .SelectMany(value => new Formula[]
            {
                new Formula.Bind(value, FormulaIdentifier.Create("x"), new Formula.Integers(), y),
                new Formula.BindMany(
                    value,
                    [
                        new Formula.BoundVariable(FormulaIdentifier.Create("x"), new Formula.Integers()),
                        new Formula.BoundVariable(FormulaIdentifier.Create("y"), new Formula.Integers()),
                    ],
                    one),
            }));
        AddRendererContextCorpus(formulas, x, y, one);
        return formulas;
    }

    private static void AddRendererContextCorpus(
        ICollection<Formula> formulas,
        Formula x,
        Formula y,
        Formula one)
    {
        var additive = new Formula.Binary(x, FormulaBinaryOperator.Add, y);
        var multiplicative = new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
        var negative = new Formula.Negate(x);
        var script = new Formula.Power(x, one);
        var scriptedAtom = new Formula.Sequence(x, y, new Formula.Integers());
        var relation = new Formula.Relation(x, FormulaRelationOperator.Equal, y);
        var logic = new Formula.Logic(x, FormulaLogicOperator.And, y);
        Formula[] representatives =
        [
            x, additive, multiplicative, negative, script, scriptedAtom, relation, logic,
        ];

        foreach (var child in representatives)
        {
            formulas.Add(new Formula.Absolute(child));
            formulas.Add(new Formula.Apply(x, [child]));
            formulas.Add(new Formula.Binary(child, FormulaBinaryOperator.Add, x));
            formulas.Add(new Formula.Binary(x, FormulaBinaryOperator.Add, child));
            formulas.Add(new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                child,
                x));
            formulas.Add(new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                x,
                child));
            formulas.Add(new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("x"), child)],
                x));
            formulas.Add(new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("x"), x)],
                child));
            formulas.Add(new Formula.Fraction(child, x));
            formulas.Add(new Formula.Fraction(x, child));
            formulas.Add(new Formula.FunctionCall(FormulaIdentifier.Create("f"), [child]));
            formulas.Add(new Formula.LatexSequence([child]));
            formulas.Add(new Formula.Layout(FormulaLayoutMode.Display, child));
            formulas.Add(new Formula.Logic(child, FormulaLogicOperator.And, x));
            formulas.Add(new Formula.Logic(x, FormulaLogicOperator.And, child));
            formulas.Add(new Formula.Modulo(child, one));
            formulas.Add(new Formula.Norm(child));
            formulas.Add(new Formula.Not(child));
            formulas.Add(new Formula.Relation(child, FormulaRelationOperator.Equal, x));
            formulas.Add(new Formula.Relation(x, FormulaRelationOperator.Equal, child));
            formulas.Add(new Formula.Sequence(child, x, new Formula.Integers()));
            formulas.Add(new Formula.SetBuilder(child, x, new Formula.Integers()));
            formulas.Add(new Formula.Subscript(x, child));
            formulas.Add(new Formula.TypeArrow(x, child));
        }

        // Repository formulas use a relation as the domain of a type arrow.
        formulas.Add(new Formula.TypeArrow(relation, x));

        var function = new Formula.FunctionCall(FormulaIdentifier.Create("f"), [x]);
        var subscript = new Formula.Subscript(x, one);
        var digits = new Formula.LatexDigits([1]);
        var group = new Formula.LatexGroup([x]);
        var sequence = new Formula.LatexSequence([x]);
        var word = new Formula.LatexWord(FormulaIdentifier.Create("word"));
        // Repository formulas apply subscripted functions such as H_c(p, q).
        formulas.Add(new Formula.Apply(subscript, [x]));
        formulas.Add(new Formula.Power(additive, x));
        formulas.Add(new Formula.Power(multiplicative, x));
        formulas.Add(new Formula.Power(script, function));
        formulas.Add(new Formula.Power(x, additive));
        formulas.Add(new Formula.Power(x, multiplicative));
        formulas.Add(new Formula.Power(x, script));
        formulas.Add(new Formula.Power(additive, function));
        formulas.Add(new Formula.Power(function, additive));
        formulas.Add(new Formula.Power(function, function));
        formulas.Add(new Formula.Power(function, one));
        formulas.Add(new Formula.Power(function, script));
        formulas.Add(new Formula.Power(function, subscript));
        // 仓库实际使用的 Power 子组合,由 AssertRendererVocabularyCoverage 点名要求覆盖。
        formulas.Add(new Formula.Power(function, sequence));
        formulas.Add(new Formula.Power(function, x));
        formulas.Add(new Formula.Power(one, one));
        formulas.Add(new Formula.Power(digits, group));
        formulas.Add(new Formula.Power(digits, sequence));
        formulas.Add(new Formula.Power(digits, word));
        formulas.Add(new Formula.Power(new Formula.Absolute(x), word));
        formulas.Add(new Formula.Power(
            new Formula.LatexMacro(FormulaLatexMacro.Phi),
            sequence));
        formulas.Add(new Formula.Power(
            new Formula.LatexMacro(FormulaLatexMacro.Phi),
            word));
        formulas.Add(new Formula.Power(sequence, group));
        formulas.Add(new Formula.Power(sequence, digits));
        formulas.Add(new Formula.Power(sequence, sequence));
        formulas.Add(new Formula.Power(sequence, word));
        formulas.Add(new Formula.Power(word, digits));
        formulas.Add(new Formula.Power(word, group));
        formulas.Add(new Formula.Power(word, word));
        formulas.Add(new Formula.Power(one, x));
        formulas.Add(new Formula.Power(new Formula.Phi(), one));
        formulas.Add(new Formula.Power(new Formula.Phi(), x));
        formulas.Add(new Formula.Power(x, y));
        formulas.Add(new Formula.LatexGroup([script]));

        formulas.Add(new Formula.Subscript(
            new Formula.LatexMacro(FormulaLatexMacro.Phi),
            sequence));
        formulas.Add(new Formula.Subscript(word, digits));
        formulas.Add(new Formula.Subscript(
            word,
            new Formula.LatexMacro(FormulaLatexMacro.Phi)));
        formulas.Add(new Formula.Subscript(word, sequence));
        // 仓库实际使用:ℝ_{≥0} 之类「序列底、序列标」的下标(EscapeSpectrum 预算包络)。
        formulas.Add(new Formula.Subscript(sequence, sequence));
        formulas.Add(new Formula.Subscript(
            word,
            new Formula.LatexSymbol(FormulaLatexSymbol.Plus)));
        formulas.Add(new Formula.Subscript(word, word));
        formulas.Add(new Formula.Subscript(word, subscript));
    }

    private static IReadOnlySet<string> RendererVocabulary(
        IEnumerable<ScribeDocument> documents,
        IEnumerable<Formula> standaloneFormulas)
    {
        var vocabulary = new HashSet<string>(StringComparer.Ordinal);
        foreach (var document in documents)
        {
            vocabulary.Add("document");
            VisitBlocks(document.Content, vocabulary);
            foreach (var edge in DocumentGraphAssembler.Extract(document))
            {
                vocabulary.Add("edge:" + edge.GetType().Name);
                if (edge is DocumentEdge.NarrativeReference narrative)
                {
                    vocabulary.Add("narrative-target:" + narrative.Target.GetType().Name);
                }
            }
        }
        foreach (var formula in standaloneFormulas)
        {
            VisitFormula(formula, vocabulary);
        }
        return vocabulary;
    }

    private static void VisitBlocks(BlockSequence blocks, ISet<string> vocabulary)
    {
        foreach (var block in blocks.Items)
        {
            vocabulary.Add("block:" + block.GetType().Name);
            switch (block)
            {
                case DocumentBlock.Paragraph paragraph:
                    foreach (var inline in paragraph.Content.Items)
                    {
                        vocabulary.Add("inline:" + inline.GetType().Name);
                        if (inline is Inline.InlineFormula formula)
                        {
                            VisitFormula(formula.Value, vocabulary);
                        }
                    }
                    break;
                case DocumentBlock.DisplayFormula display:
                    VisitFormula(display.Value, vocabulary);
                    break;
                case DocumentBlock.Section section:
                    VisitBlocks(section.Content, vocabulary);
                    break;
                case DocumentBlock.Describe describe:
                    vocabulary.Add(
                        $"describe:kind={describe.Kind};provenance={describe.ProvenanceKind};"
                            + $"statement={describe.Statement.GetType().Name}");
                    if (describe.StatementFormula is { } statementFormula)
                    {
                        VisitFormula(statementFormula, vocabulary);
                    }
                    VisitBlocks(describe.Content, vocabulary);
                    break;
            }
        }
    }

    private static void VisitFormula(Formula formula, ISet<string> vocabulary)
    {
        var type = formula.GetType();
        vocabulary.Add("formula:" + type.Name);
        switch (formula)
        {
            case Formula.Power power:
                vocabulary.Add(
                    $"formula-children:Power(Base={power.Base.GetType().Name},"
                        + $"Exponent={power.Exponent.GetType().Name})");
                break;
            case Formula.Subscript subscript:
                vocabulary.Add(
                    $"formula-children:Subscript(Base={subscript.Base.GetType().Name},"
                        + $"Index={subscript.Index.GetType().Name})");
                break;
        }
        foreach (var property in type.GetProperties(BindingFlags.Instance | BindingFlags.Public))
        {
            var value = property.GetValue(formula);
            switch (value)
            {
                case Formula child:
                    vocabulary.Add(FormulaContext(type.Name, property.Name, child));
                    VisitFormula(child, vocabulary);
                    break;
                case IEnumerable<Formula> children:
                    foreach (var item in children)
                    {
                        vocabulary.Add(FormulaContext(type.Name, property.Name, item));
                        VisitFormula(item, vocabulary);
                    }
                    break;
                case IEnumerable<Formula.BoundVariable> variables:
                    foreach (var variable in variables)
                    {
                        vocabulary.Add(FormulaContext(type.Name, property.Name + ".Domain", variable.Domain));
                        VisitFormula(variable.Domain, vocabulary);
                    }
                    break;
                case Enum discriminator:
                    vocabulary.Add($"formula-enum:{type.Name}.{property.Name}={discriminator}");
                    break;
            }
        }
    }

    private static string FormulaContext(string parent, string role, Formula child) =>
        $"formula-context:{parent}.{role}={FormulaRenderingTraits(child)}";

    private static string FormulaRenderingTraits(Formula formula) =>
        $"precedence:{FormulaPrecedence(formula)};"
            + $"produces-script:{ProducesScript(formula).ToString().ToLowerInvariant()};"
            + $"starts-with-negation:{StartsWithNegation(formula).ToString().ToLowerInvariant()}";

    private static string FormulaPrecedence(Formula formula) => formula switch
    {
        Formula.Logic or Formula.Not or Formula.Bind => "logic",
        Formula.Relation or Formula.RelationChain or Formula.TypeArrow => "relation",
        Formula.Binary { Operator: FormulaBinaryOperator.Add or FormulaBinaryOperator.Subtract } => "additive",
        Formula.Binary or Formula.Modulo => "multiplicative",
        Formula.Negate => "prefix",
        Formula.Subscript or Formula.Power => "script",
        _ => "atom",
    };

    private static bool ProducesScript(Formula formula) =>
        formula is Formula.Subscript or Formula.Power or Formula.Sequence;

    private static bool StartsWithNegation(Formula formula) => formula switch
    {
        Formula.Negate => true,
        Formula.Binary { Operator: FormulaBinaryOperator.Multiply } binary =>
            StartsWithNegation(binary.Left),
        Formula.Modulo modulo => StartsWithNegation(modulo.Value),
        _ => false,
    };

    private static void AssertClosedFormulaVocabularyIsCovered(IReadOnlySet<string> vocabulary)
    {
        var missingTypes = typeof(Formula)
            .GetNestedTypes(BindingFlags.Public)
            .Where(static type => typeof(Formula).IsAssignableFrom(type))
            .Select(static type => "formula:" + type.Name)
            .Except(vocabulary, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            missingTypes.Length == 0,
            "The fixed renderer corpus omits closed Formula node types: "
                + string.Join(", ", missingTypes));
    }

    private static string FormulaKey(Formula formula) => formula switch
    {
        Formula.LatexMacro macro => $"{formula.GetType().Name}:{macro.Value}",
        Formula.LatexSymbol symbol => $"{formula.GetType().Name}:{symbol.Value}",
        Formula.Binary binary => $"{formula.GetType().Name}:{binary.Operator}",
        Formula.Relation relation => $"{formula.GetType().Name}:{relation.Operator}",
        Formula.RelationChain chain => $"{formula.GetType().Name}:{chain.Operator}",
        Formula.Logic logic => $"{formula.GetType().Name}:{logic.Operator}",
        Formula.Bind bind => $"{formula.GetType().Name}:{bind.Quantifier}",
        Formula.BindMany bind => $"{formula.GetType().Name}:{bind.Quantifier}",
        Formula.Layout layout => $"{formula.GetType().Name}:{layout.Mode}",
        _ => formula.GetType().Name,
    };

    private static void AppendLengthPrefixed(IncrementalHash aggregate, byte[] value)
    {
        Span<byte> length = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32BigEndian(length, value.Length);
        aggregate.AppendData(length);
        aggregate.AppendData(value);
    }
}
