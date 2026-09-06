using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using System.Text.Json;
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
        var publicFactories = typeof(Describe)
            .GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Where(static method => method.ReturnType == typeof(DocumentBlock.Describe))
            .Where(HasResolutionClaimParameter)
            .Select(static method => method.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var internalFactories = typeof(DocumentBlock.Describe)
            .GetMethods(BindingFlags.NonPublic | BindingFlags.Static)
            .Where(static method => method.ReturnType == typeof(DocumentBlock.Describe))
            .Where(HasResolutionClaimParameter)
            .Select(static method => method.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal([nameof(Describe.Lean)], publicFactories);
        Assert.Equal(["ReportDerived"], internalFactories);
        Assert.All(
            typeof(Describe).GetMethods(BindingFlags.Public | BindingFlags.Static)
                .Where(static method => method.Name is nameof(Describe.Remark) or nameof(Describe.Example)),
            static method => Assert.DoesNotContain(
                method.GetParameters(),
                static parameter => parameter.ParameterType == typeof(OpenProblemResolutionClaim)));
    }

    [Fact]
    public void DescribeCarriesOneOptionalScalarResolutionClaim()
    {
        var property = typeof(DocumentBlock.Describe).GetProperty(
            nameof(DocumentBlock.Describe.OpenProblemResolutionClaim));
        var nullability = new NullabilityInfoContext().Create(property!);
        var withoutClaim = Describe.Lean(
            DescribeId.Create("without-resolution"),
            DeclarationHandle.Create(TheoremGid),
            Heading.Create("Without resolution"),
            StatementSource.FromAuthor(InlineIdentity()),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("No resolution claim."))),
            DescribeRole.Theorem);

        Assert.NotNull(property);
        Assert.Equal(typeof(OpenProblemResolutionClaim), property!.PropertyType);
        Assert.Equal(NullabilityState.Nullable, nullability.ReadState);
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
        var proved = ClaimDescribe();
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

    private static bool HasResolutionClaimParameter(MethodInfo method) =>
        method.GetParameters().Any(static parameter =>
            parameter.ParameterType == typeof(OpenProblemResolutionClaim));

    private static DocumentBlock.Describe RehydrateWithClaim(
        DocumentBlock.Describe source,
        OpenProblemResolutionClaim claim)
    {
        var constructor = typeof(DocumentBlock.Describe)
            .GetConstructors(BindingFlags.Instance | BindingFlags.NonPublic)
            .Single(static candidate => candidate.GetParameters().Length == 10);
        return (DocumentBlock.Describe)constructor.Invoke(
        [
            source.Id,
            source.Kind,
            source.Title,
            source.Statement,
            source.AssessedProvenance,
            source.Content,
            source.StatementFormula,
            source.KindSource,
            source.StatementSource,
            claim,
        ]);
    }

    private static DocumentBlock.Describe ClaimDescribe(
        string id = "resolution",
        string declarationGid = TheoremGid,
        string slug = ProblemSlug,
        ResolutionKind resolutionKind = ResolutionKind.Proved,
        DescribeRole? role = DescribeRole.Theorem,
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
