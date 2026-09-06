using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using System.Text;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class OpenProblemResolutionClaimTests
{
    private const string ProblemSlug = "sample-open-problem";
    private const string ModuleGid = "D5/S1/Phase/Basic";
    private const string FormalPath = ModuleGid + ".lean";
    private const string TheoremGid = ModuleGid + ".resolution_theorem";

    [Theory]
    [InlineData("")]
    [InlineData("Sample-open-problem")]
    [InlineData("sample_open_problem")]
    [InlineData("sample--open-problem")]
    [InlineData("sample-open-problem.md")]
    public void ProblemSlugRefRejectsValuesOutsideTheProblemPoolGrammar(string value)
    {
        Assert.False(ProblemPoolPaths.IsCanonicalSlug(value));
        Assert.Throws<ArgumentException>(() => ProblemSlugRef.Create(value));
    }

    [Fact]
    public void ValidatorRejectsClaimWhoseSlugIsAbsentFromCurrentProblemCatalog()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe(slug: "missing-open-problem"));
            var report = Report((TheoremGid, "theorem"));

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "dangling-problem-slug");
            Assert.Contains("resolves to 0 current problem dossiers", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsClaimWhoseSlugIsAmbiguousInCurrentProblemCatalog()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());
            var report = Report((TheoremGid, "theorem"));
            var inspected = ProblemCandidateCatalog.Inspect(root);
            var candidate = Assert.Single(inspected.Candidates);
            var ambiguous = new ProblemCandidateCatalogInspection(
                [candidate, candidate with { RelativePath = "Problems/duplicate-fixture.md" }],
                inspected.Findings);

            var findings = DescribeRepositoryValidator.Validate(
                root,
                [document],
                report,
                problemInspection: ambiguous);

            var finding = Assert.Single(findings, static item =>
                item.Code == "dangling-problem-slug");
            Assert.Contains("resolves to 2 current problem dossiers", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsResolutionClaimWhoseLeanDeclarationIsNotTheoremLike()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());
            var report = Report((TheoremGid, "def"));

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "invalid-problem-resolution-source");
            Assert.Contains("theorem-like", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsResolutionClaimWhoseScribeRoleIsNotTheoremLike()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe(role: DescribeRole.Definition));
            var report = Report((TheoremGid, "theorem"));

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "invalid-problem-resolution-source");
            Assert.Contains("theorem-like", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsResolutionClaimWhoseHostIsNotFrozen()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());
            var report = Report((TheoremGid, "theorem"));
            DeleteFrozenState(root);

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "invalid-problem-resolution-source"
                && item.Message.Contains("not a member of frozen state", StringComparison.Ordinal));
            Assert.Contains(TheoremGid, finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorUsesExactFrozenStatementResolutionRatherThanModuleOnlyMembership()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());
            var report = ReportWithNameKey(
                TheoremGid,
                "theorem",
                "another_theorem");

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "invalid-problem-resolution-source"
                && item.Message.Contains("0 current report declarations", StringComparison.Ordinal));
            Assert.Contains(TheoremGid, finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsSecondResolutionClaimForTheSameProblemSlug()
    {
        WithRepository(root =>
        {
            const string secondGid = ModuleGid + ".second_resolution_theorem";
            var document = CreateDocument(
                ClaimDescribe(),
                ClaimDescribe(
                    id: "second-resolution",
                    declarationGid: secondGid,
                    resolutionKind: ResolutionKind.Refuted));
            var report = Report(
                (TheoremGid, "theorem"),
                (secondGid, "theorem"));

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings, static item =>
                item.Code == "duplicate-problem-resolution-claim");
            Assert.Contains(ProblemSlug, finding.Message, StringComparison.Ordinal);
            Assert.Contains("second-resolution", finding.Path, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsResolutionClaimWhenLeanReportIsUnavailable()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            var finding = Assert.Single(findings, static item =>
                item.Code == "missing-problem-resolution-lean-report");
            Assert.Contains("compiled-artifact report", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ResolutionClaimFactoriesAreClosedAwayFromRemarksAndAuthoredFormulaNodes()
    {
        var symbols = DescribeSymbols();
        var publicMethods = symbols.Factories.GetMembers().OfType<IMethodSymbol>()
            .Where(static method => method.IsStatic
                && method.DeclaredAccessibility == Accessibility.Public)
            .ToArray();
        var publicFactories = publicMethods
            .Where(method => SymbolEqualityComparer.Default.Equals(method.ReturnType, symbols.Describe))
            .Where(method => HasResolutionClaimParameter(method, symbols.Claim))
            .Select(static method => method.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var internalFactories = symbols.Describe.GetMembers().OfType<IMethodSymbol>()
            .Where(static method => method.IsStatic)
            .Where(method => SymbolEqualityComparer.Default.Equals(method.ReturnType, symbols.Describe))
            .Where(method => HasResolutionClaimParameter(method, symbols.Claim))
            .Select(static method => method.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal([nameof(Describe.Lean)], publicFactories);
        Assert.Equal(["ReportDerived"], internalFactories);
        Assert.All(
            publicMethods
                .Where(static method => method.Name is nameof(Describe.Remark) or nameof(Describe.Example)),
            method => Assert.False(HasResolutionClaimParameter(method, symbols.Claim)));
    }

    [Fact]
    public void DescribeCarriesOneOptionalScalarResolutionClaim()
    {
        var symbols = DescribeSymbols();
        var property = Assert.Single(symbols.Describe
            .GetMembers(nameof(DocumentBlock.Describe.OpenProblemResolutionClaim))
            .OfType<IPropertySymbol>());
        var withoutClaim = Describe.Lean(
            DescribeId.Create("without-resolution"),
            DeclarationHandle.Create(TheoremGid),
            Heading.Create("Without resolution"),
            StatementSource.FromAuthor(InlineIdentity()),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("No resolution claim."))),
            DescribeRole.Theorem);

        Assert.Equal(Accessibility.Public, property.DeclaredAccessibility);
        Assert.False(property.IsStatic);
        Assert.NotNull(property.GetMethod);
        Assert.Equal(Accessibility.Public, property.GetMethod.DeclaredAccessibility);
        Assert.True(SymbolEqualityComparer.Default.Equals(symbols.Claim, property.Type));
        Assert.Equal(NullableAnnotation.Annotated, property.NullableAnnotation);
        Assert.DoesNotContain(
            property.GetAttributes().Concat(property.GetMethod.GetReturnTypeAttributes()),
            static attribute => attribute.AttributeClass?.ToDisplayString()
                == "System.Diagnostics.CodeAnalysis.NotNullAttribute");
        Assert.Null(withoutClaim.OpenProblemResolutionClaim);
    }

    [Fact]
    public void ProblemSlugAndResolutionClaimHaveCanonicalValueEquality()
    {
        var firstSlug = ProblemSlugRef.Create(ProblemSlug);
        var secondSlug = ProblemSlugRef.Create(ProblemSlug);
        var first = new OpenProblemResolutionClaim(firstSlug, ResolutionKind.Proved);
        var second = new OpenProblemResolutionClaim(secondSlug, ResolutionKind.Proved);

        Assert.Equal(firstSlug, secondSlug);
        Assert.Equal(firstSlug.GetHashCode(), secondSlug.GetHashCode());
        Assert.Equal(first, second);
        Assert.Equal(
            [ResolutionKind.Proved, ResolutionKind.Refuted],
            Enum.GetValues<ResolutionKind>());
    }

    [Fact]
    public void DescribeValueEqualityIncludesResolutionClaim()
    {
        var proved = ClaimDescribe(role: DescribeRole.Theorem);
        var provedTwin = RehydrateWithClaim(
            proved,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(ProblemSlug),
                ResolutionKind.Proved));
        var refuted = RehydrateWithClaim(
            proved,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(ProblemSlug),
                ResolutionKind.Refuted));

        Assert.Equal(proved, provedTwin);
        Assert.NotEqual(proved, refuted);
    }

    [Fact]
    public void ResolutionClaimRejectsUnknownResolutionKind()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() =>
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(ProblemSlug),
                (ResolutionKind)int.MaxValue));
    }

    [Fact]
    public void ResolutionClaimSurvivesNestedDeclarationResolution()
    {
        var expected = new OpenProblemResolutionClaim(
            ProblemSlugRef.Create(ProblemSlug),
            ResolutionKind.Proved);
        var document = CreateDocument(ClaimDescribe(claim: expected));
        var catalog = DeclarationCatalog.Create(Report((TheoremGid, "theorem")));

        var resolved = document.ResolveDeclarations(catalog);

        var section = Assert.IsType<DocumentBlock.Section>(Assert.Single(resolved.Content.Items));
        var describe = Assert.IsType<DocumentBlock.Describe>(Assert.Single(section.Content.Items));
        Assert.Equal(expected, describe.OpenProblemResolutionClaim);
        Assert.Equal(DescribeKind.Theorem, describe.Kind);
    }

    [Fact]
    public void DescribeReportProjectsResolutionClaimAsTypedFields()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe(resolutionKind: ResolutionKind.Refuted));
            var report = Report((TheoremGid, "theorem"));

            var json = DescribeReportWriter.WriteJson(DescribeReport.Build(root, [document], report));

            using var parsed = JsonDocument.Parse(json);
            Assert.Equal(
                "scribe-describe-report-v2",
                parsed.RootElement.GetProperty("schema").GetString());
            var resolution = Assert.Single(parsed.RootElement.GetProperty("nodes").EnumerateArray())
                .GetProperty("open_problem_resolution");
            Assert.Equal(ProblemSlug, resolution.GetProperty("problem_slug").GetString());
            Assert.Equal("refuted", resolution.GetProperty("resolution_kind").GetString());
        });
    }

    [Fact]
    public void DescribeReportResolvesDefaultRoleBeforeProjectingResolutionClaim()
    {
        WithRepository(root =>
        {
            var claim = new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(ProblemSlug), ResolutionKind.Proved);
            var describe = Describe.Lean(
                DescribeId.Create("resolution"),
                DeclarationHandle.Create(TheoremGid),
                Heading.Create("Resolution"),
                StatementSource.FromAuthor(InlineIdentity()),
                AssessedProvenance.FromRepo(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Resolution."))),
                openProblemResolutionClaim: claim);

            var report = DescribeReport.Build(
                root, [CreateDocument(describe)], Report((TheoremGid, "theorem")));

            Assert.Equal("classified", report.Status);
            Assert.Empty(report.RedFindings);
            var node = Assert.Single(report.Nodes);
            Assert.Equal("theorem", node.Kind);
            Assert.Equal(claim, node.OpenProblemResolutionClaim);
            using var json = JsonDocument.Parse(DescribeReportWriter.WriteJson(report));
            var projected = Assert.Single(json.RootElement.GetProperty("nodes").EnumerateArray());
            Assert.Equal("theorem", projected.GetProperty("kind").GetString());
            var resolution = projected.GetProperty("open_problem_resolution");
            Assert.Equal(ProblemSlug, resolution.GetProperty("problem_slug").GetString());
            Assert.Equal("proved", resolution.GetProperty("resolution_kind").GetString());
        });
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DescribeReportRejectsDefaultRoleClaimWithoutLeanReport(bool validateContentGovernance)
    {
        WithRepository(root =>
        {
            var describe = Describe.Lean(
                DescribeId.Create("resolution"),
                DeclarationHandle.Create(TheoremGid),
                Heading.Create("Resolution"),
                StatementSource.FromAuthor(InlineIdentity()),
                AssessedProvenance.FromRepo(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Resolution."))),
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(ProblemSlug), ResolutionKind.Proved));

            var report = DescribeReport.Build(
                root, [CreateDocument(describe)], validateContentGovernance: validateContentGovernance);

            Assert.Equal("invalid", report.Status);
            Assert.Contains(report.RedFindings, static finding =>
                finding.Code == "missing-problem-resolution-lean-report");
            Assert.Empty(report.Nodes);
        });
    }

    [Fact]
    public void ReviewNestedDescribeRejectsMissingDossier() => WithRepository(root =>
    {
        var document = CreateDocument(Nest(ClaimDescribe(slug: "missing-open-problem")));
        var findings = DescribeRepositoryValidator.Validate(root, [document], Report((TheoremGid, "theorem")));
        Assert.Contains(findings, f => f.Code == "dangling-problem-slug");
    });

    [Fact]
    public void ReviewNestedDescribeRejectsDuplicateClaim() => WithRepository(root =>
    {
        var document = CreateDocument(ClaimDescribe(), Nest(ClaimDescribe(id: "nested")));
        var findings = DescribeRepositoryValidator.Validate(root, [document], Report((TheoremGid, "theorem")));
        Assert.Single(findings, f => f.Code == "duplicate-problem-resolution-claim");
    });

    [Fact]
    public void ReviewNestedClaimReportFailsClosedWithoutLeanReport() => WithRepository(root =>
    {
        var report = DescribeReport.Build(root,
            [CreateDocument(Nest(ClaimDescribe(role: DescribeRole.Theorem)))]);
        Assert.Equal("invalid", report.Status);
        Assert.Contains(report.RedFindings, f => f.Code == "missing-problem-resolution-lean-report");
    });

    [Fact]
    public void ClaimDescribeDefaultsIdToResolution() =>
        Assert.Equal("resolution", ClaimDescribe().Id.Value);

    [Fact]
    public void ClaimDescribeDefaultsDeclarationToFixtureTheorem() =>
        Assert.Equal(TheoremGid,
            Assert.IsType<DescribeStatement.LeanDeclaration>(ClaimDescribe().Statement).Value.Value);

    [Fact]
    public void ClaimDescribeDefaultsSlugToFixtureProblem() =>
        Assert.Equal(ProblemSlug, ClaimDescribe().OpenProblemResolutionClaim!.ProblemSlug.Value);

    [Fact]
    public void ClaimDescribeDefaultsResolutionKindToProved() =>
        Assert.Equal(ResolutionKind.Proved, ClaimDescribe().OpenProblemResolutionClaim!.ResolutionKind);

    [Fact]
    public void ClaimDescribeDefaultsRoleToProductionDefault() =>
        Assert.Null(Assert.IsType<DescribeKindSource.ReportDerived>(ClaimDescribe().KindSource).Role);

    [Fact]
    public void ClaimDescribeDefaultsClaimToFixtureResolution() =>
        Assert.Equal(new OpenProblemResolutionClaim(ProblemSlugRef.Create(ProblemSlug), ResolutionKind.Proved),
            ClaimDescribe().OpenProblemResolutionClaim);

    [Fact]
    public void CanonicalMarkdownWriterEmitsClosedVersionedResolutionMarker()
    {
        var document = CreateDocument(ClaimDescribe());
        var catalog = DeclarationCatalog.Create(Report((TheoremGid, "theorem")));

        var markdown = Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(document, catalog).AsSpan());

        Assert.Contains(
            "*Resolves.* `Problems/sample-open-problem` (proved).\n\n"
            + "<!-- scribe-open-problem-resolution-v1 "
            + "{\"problem_slug\":\"sample-open-problem\",\"resolution_kind\":\"proved\"} -->",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ValidatorAcceptsOneCurrentDossierBoundToOneFrozenTheoremDeclaration()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(ClaimDescribe());
            var report = Report((TheoremGid, "theorem"));

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            Assert.Empty(findings);
        });
    }

    private static bool HasResolutionClaimParameter(IMethodSymbol method, INamedTypeSymbol claim) =>
        method.Parameters.Any(parameter => SymbolEqualityComparer.Default.Equals(parameter.Type, claim));

    private static (INamedTypeSymbol Factories, INamedTypeSymbol Describe, INamedTypeSymbol Claim) DescribeSymbols()
    {
        // Inspect the loaded binary, including private factories, without invoking reflected code.
        var reference = MetadataReference.CreateFromFile(typeof(Describe).Assembly.Location);
        var compilation = CSharpCompilation.Create(
            "ResolutionClaimContract",
            references: [reference, MetadataReference.CreateFromFile(typeof(object).Assembly.Location)],
            options: new CSharpCompilationOptions(
                OutputKind.DynamicallyLinkedLibrary,
                metadataImportOptions: MetadataImportOptions.All));
        var assembly = Assert.IsAssignableFrom<IAssemblySymbol>(compilation.GetAssemblyOrModuleSymbol(reference));
        return (
            Assert.IsAssignableFrom<INamedTypeSymbol>(assembly.GetTypeByMetadataName("StrataLint.Scribe.Describe")),
            Assert.IsAssignableFrom<INamedTypeSymbol>(assembly.GetTypeByMetadataName("StrataLint.Scribe.DocumentBlock+Describe")),
            Assert.IsAssignableFrom<INamedTypeSymbol>(assembly.GetTypeByMetadataName("StrataLint.Scribe.OpenProblemResolutionClaim")));
    }

    private static DocumentBlock.Describe RehydrateWithClaim(
        DocumentBlock.Describe source,
        OpenProblemResolutionClaim claim) =>
        ConstructDescribe(
            source.Id,
            source.Kind,
            source.Title,
            source.Statement,
            source.AssessedProvenance,
            source.Content,
            source.StatementFormula,
            source.KindSource,
            source.StatementSource,
            claim);

    // Pin the constructor signature so equality fixtures differ only in their claim argument.
    [UnsafeAccessor(UnsafeAccessorKind.Constructor)]
    private static extern DocumentBlock.Describe ConstructDescribe(
        DescribeId id,
        DescribeKind? kind,
        Heading title,
        DescribeStatement statement,
        AssessedProvenance assessedProvenance,
        BlockSequence content,
        Formula? statementFormula,
        DescribeKindSource? kindSource,
        StatementSource? statementSource,
        OpenProblemResolutionClaim? openProblemResolutionClaim);

    private static DocumentBlock.Describe ClaimDescribe(
        string id = "resolution",
        string declarationGid = TheoremGid,
        string slug = ProblemSlug,
        ResolutionKind resolutionKind = ResolutionKind.Proved,
        DescribeRole? role = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(declarationGid),
            Heading.Create("Resolution"),
            StatementSource.FromAuthor(InlineIdentity()),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed resolution narrative."))),
            role,
            claim ?? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(slug),
                resolutionKind));

    private static DocumentBlock.Describe Nest(params DocumentBlock.Describe[] children) =>
        Describe.Remark(DescribeId.Create("parent"), Heading.Create("Parent"), InlineIdentity(),
            AssessedProvenance.FromRepo(), DefinitionDsl.Blocks(children));

    private static ScribeDocument CreateDocument(params DocumentBlock.Describe[] describes) =>
        ScribeDocument.Create(
            DefinitionDsl.Header(ModuleGid, "Resolution claim fixture."),
            Heading.Create("Resolution claims"),
            DefinitionDsl.Blocks(new DocumentBlock.Section(
                Heading.Create("Results"),
                DefinitionDsl.Blocks(describes))));

    private static Formula InlineIdentity() => new Formula.Layout(
        FormulaLayoutMode.Inline,
        new Formula.Relation(
            new Formula.Symbol(FormulaIdentifier.Create("x")),
            FormulaRelationOperator.Equal,
            new Formula.Symbol(FormulaIdentifier.Create("x"))));

    private static LeanAxiomReport Report(params (string Gid, string Kind)[] declarations) =>
        ReportWithNameKeys(declarations.Select(static item =>
        {
            var canonicalName = item.Gid.Replace('/', '.');
            var shortName = canonicalName[(canonicalName.LastIndexOf('.') + 1)..];
            return (item.Gid, item.Kind, NameKeyShortName: shortName);
        }));

    private static LeanAxiomReport ReportWithNameKey(
        string gid,
        string kind,
        string nameKeyShortName) =>
        ReportWithNameKeys([(gid, kind, nameKeyShortName)]);

    private static LeanAxiomReport ReportWithNameKeys(
        IEnumerable<(string Gid, string Kind, string NameKeyShortName)> declarations) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [FormalPath] = new LeanFileReport(
                [],
                declarations.Select(static item =>
                {
                    var canonicalName = item.Gid.Replace('/', '.');
                    return new LeanDeclaration(
                        canonicalName,
                        item.Kind,
                        $"statement-v1(source={item.Gid})",
                        ImmutableArray.Create("propext", "Classical.choice", "Quot.sound"))
                    {
                        NameKey = $"ns(n0,{Encoding.UTF8.GetByteCount(item.NameKeyShortName)}:"
                            + $"{item.NameKeyShortName})",
                    };
                })
                .ToImmutableArray()),
        });

    private static void WithRepository(Action<string> assertion)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-resolution-" + Guid.NewGuid().ToString("N"));
        var encoding = new UTF8Encoding(false, true);
        try
        {
            Write(root, FormalPath, "-- resolution fixture\n", encoding);
            Write(
                root,
                "Golden/Frozen/state/" + FormalPath + ".json",
                "{\"statement_id\":\"sha256:" + new string('d', 64) + "\"}\n",
                encoding);
            Write(root, "Problems/" + ProblemSlug + ".md", Candidate(), encoding);
            Write(root, "Library/notes/sos1957threegap.md", Note(), encoding);
            assertion(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    private static void DeleteFrozenState(string root) =>
        TemporaryFileSystem.Directory.Delete(
            Path.Combine(root, "Golden", "Frozen"),
            recursive: true);

    private static void Write(string root, string relativePath, string content, Encoding encoding)
    {
        var path = Path.Combine(
            root,
            relativePath.Replace('/', Path.DirectorySeparatorChar));
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, content, encoding);
    }

    private static string Note() =>
        "---\n"
        + "bibkey: sos1957threegap\n"
        + "authors: Vera T. Sos\n"
        + "year: 1957\n"
        + "title: On the three gap theorem\n"
        + "doi: 10.48550/arXiv.2305.08349\n"
        + "claim: Gap lengths for irrational rotations.\n"
        + "strata_touched: []\n"
        + "license: citation-only\n"
        + "triage: anchor\n"
        + "---\n";

    private static string Candidate() =>
        "---\n"
        + $"slug: {ProblemSlug}\n"
        + "bibkey: sos1957threegap\n"
        + "arxiv_id: 2305.08349\n"
        + "triage: theorem\n"
        + "motivation_gids:\n"
        + $"  - {ModuleGid}\n"
        + "---\n\n"
        + "# Sample open problem\n\n"
        + "## Problem\n\nProve the sample statement.\n\n"
        + "## Motivation\n\nThe frozen phase layer supplies the setup.\n\n"
        + "## Gap\n\nThe theorem is not in the cited source.\n\n"
        + "## Route\n\nClose the remaining argument.\n\n"
        + "## Falsifier\n\nA counterexample refutes it.\n\n"
        + "## Evidence\n\nThe cited paper states the problem.\n\n"
        + "## Triage\n\nThe statement is theorem-shaped.\n\n"
        + "## ASSUMED-UNVERIFIED\n\n"
        + "- Whether the problem was resolved after the cited version.\n";
}
