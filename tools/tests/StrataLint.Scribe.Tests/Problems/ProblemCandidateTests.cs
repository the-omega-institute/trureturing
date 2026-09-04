using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ProblemCandidateTests
{
    [Fact]
    public void CatalogParsesCanonicalFrontMatterAndSections()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem"),
            },
            root =>
            {
                var candidate = Assert.Single(ProblemCandidateCatalog.Load(root).Candidates);
                Assert.Equal("sample-open-problem", candidate.Slug);
                Assert.Equal("sos1957threegap", candidate.BibKey.Value);
                Assert.Equal("2305.08349", candidate.ArxivId);
                Assert.Equal(ProblemTriage.Theorem, candidate.Triage);
                Assert.Equal(
                    "D5/S1/Phase/Basic",
                    Assert.Single(candidate.MotivationGids).Value);
                Assert.Equal("Problems/sample-open-problem.md", candidate.RelativePath);
            });
    }

    [Fact]
    public void CatalogRejectsSlugThatDisagreesWithItsPath()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("another-slug"),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("slug disagrees with its path", error.Message, StringComparison.Ordinal);
            });
    }

    [Theory]
    [InlineData("slug")]
    [InlineData("bibkey")]
    [InlineData("arxiv_id")]
    [InlineData("triage")]
    [InlineData("motivation_gids")]
    public void CatalogRejectsAMissingRequiredField(string field)
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = WithoutFrontMatterKey(
                    Candidate("sample-open-problem"),
                    field),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains(
                    "missing or unknown metadata fields",
                    error.Message,
                    StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsAnUnknownFrontMatterField()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem")
                    .Replace("triage: theorem\n", "triage: theorem\nstatus: candidate\n", StringComparison.Ordinal),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains(
                    "missing or unknown metadata fields",
                    error.Message,
                    StringComparison.Ordinal);
            });
    }

    [Theory]
    [InlineData("open")]
    [InlineData("Theorem")]
    [InlineData("")]
    public void CatalogRejectsATriageOutsideTheClosedAlphabet(string triage)
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem", triage: triage),
            },
            root => Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root)));
    }

    [Theory]
    [InlineData("arXiv:2305.08349")]
    [InlineData("2305.08349v1")]
    [InlineData("2305.083491")]
    [InlineData("")]
    public void CatalogRejectsANoncanonicalArxivId(string arxivId)
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem", arxivId: arxivId),
            },
            root => Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root)));
    }

    [Fact]
    public void CatalogRejectsANoncanonicalBibkey()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem", bibkey: "Sos1957threegap"),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("noncanonical bibkey", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsAnEmptyOrDuplicatedMotivationChain()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem", motivationGids: []),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("motivation_gids", error.Message, StringComparison.Ordinal);
            });

        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate(
                    "sample-open-problem",
                    motivationGids: ["D5/S1/Phase/Basic", "D5/S1/Phase/Basic"]),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("duplicate", error.Message, StringComparison.Ordinal);
            });
    }

    [Theory]
    [InlineData("Problem")]
    [InlineData("Motivation")]
    [InlineData("Gap")]
    [InlineData("Route")]
    [InlineData("Falsifier")]
    [InlineData("Evidence")]
    [InlineData("Triage")]
    [InlineData("ASSUMED-UNVERIFIED")]
    public void CatalogRejectsAMissingRequiredSection(string section)
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = WithoutSection(
                    Candidate("sample-open-problem"),
                    section),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains(section, error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsAnEmptyRequiredSection()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem")
                    .Replace(
                        "## Falsifier\n\nA concrete counterexample refutes it.\n",
                        "## Falsifier\n\n",
                        StringComparison.Ordinal),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("Falsifier", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsAnUnknownSection()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem")
                    + "\n## Appendix\n\nExtra prose.\n",
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("Appendix", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsAnAggregateIndexFile()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem"),
                ["index.md"] = "# Problem pool\n\n- sample-open-problem\n",
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("index.md", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogRejectsCarriageReturnsAndByteOrderMarks()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = Candidate("sample-open-problem")
                    .Replace("\n", "\r\n", StringComparison.Ordinal),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("BOM or CR", error.Message, StringComparison.Ordinal);
            });

        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sample-open-problem.md"] = "﻿" + Candidate("sample-open-problem"),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
                Assert.Contains("BOM or CR", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void CatalogReportsEveryOffendingFileRatherThanStoppingAtTheFirst()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["first-problem.md"] = Candidate("first-problem", triage: "open"),
                ["second-problem.md"] = Candidate("second-problem", arxivId: "bad"),
            },
            root =>
            {
                var inspection = ProblemCandidateCatalog.Inspect(root);
                Assert.Equal(2, inspection.Findings.Length);
                Assert.Equal(
                    ["Problems/first-problem.md", "Problems/second-problem.md"],
                    inspection.Findings.Select(finding => finding.Path));
            });
    }

    [Fact]
    public void CatalogIsEmptyWhenTheDirectoryIsAbsent()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-problems-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        try
        {
            var inspection = ProblemCandidateCatalog.Inspect(root);
            Assert.Empty(inspection.Candidates);
            Assert.Empty(inspection.Findings);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ValidatorAcceptsACandidateBoundToItsNoteAndFrozenChain()
    {
        WithRepository(
            Candidate("sample-open-problem"),
            Note("sos1957threegap", "10.48550/arXiv.2305.08349"),
            declarations: ["D5/S1/Phase/Basic"],
            assertion: root => Assert.Empty(DescribeRepositoryValidator.Validate(root, [])),
            frozenDeclarations: ["D5/S1/Phase/Basic"]);
    }

    [Fact]
    public void ValidatorRejectsABibkeyThatNamesNoLibraryNote()
    {
        WithRepository(
            Candidate("sample-open-problem", bibkey: "slater1967gaps"),
            Note("sos1957threegap", "10.48550/arXiv.2305.08349"),
            declarations: ["D5/S1/Phase/Basic"],
            assertion: root =>
            {
                var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, []));
                Assert.Equal("dangling-problem-bibkey", finding.Code);
                Assert.Equal("Problems/sample-open-problem.md", finding.Path);
            },
            frozenDeclarations: ["D5/S1/Phase/Basic"]);
    }

    [Fact]
    public void ValidatorRejectsAnArxivIdThatDisagreesWithTheNoteDoi()
    {
        WithRepository(
            Candidate("sample-open-problem"),
            Note("sos1957threegap", "10.48550/arXiv.2106.09959"),
            declarations: ["D5/S1/Phase/Basic"],
            assertion: root =>
            {
                var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, []));
                Assert.Equal("problem-source-mismatch", finding.Code);
                Assert.Contains("2305.08349", finding.Message, StringComparison.Ordinal);
            },
            frozenDeclarations: ["D5/S1/Phase/Basic"]);
    }

    [Fact]
    public void ValidatorRejectsAMotivationGidThatDoesNotResolve()
    {
        WithRepository(
            Candidate("sample-open-problem"),
            Note("sos1957threegap", "10.48550/arXiv.2305.08349"),
            declarations: [],
            assertion: root =>
            {
                var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, []));
                Assert.Equal("dangling-problem-gid", finding.Code);
                Assert.Contains("D5/S1/Phase/Basic", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void ValidatorRejectsAnExistingMotivationHostThatIsNotAFrozenStateMember()
    {
        WithRepository(
            Candidate("sample-open-problem"),
            Note("sos1957threegap", "10.48550/arXiv.2305.08349"),
            declarations: ["D5/S1/Phase/Basic"],
            assertion: root =>
            {
                var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, []));
                Assert.Equal("dangling-problem-gid", finding.Code);
                Assert.Contains(
                    "host selector D5/S1/Phase/Basic.lean is not a frozen state member",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    private static void WithRepository(
        string candidate,
        string note,
        IReadOnlyList<string> declarations,
        Action<string> assertion,
        IReadOnlyList<string>? frozenDeclarations = null)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-problems-" + Guid.NewGuid().ToString("N"));
        var encoding = new UTF8Encoding(false, true);
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Problems"));
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Library", "notes"));
        try
        {
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(root, "Problems", "sample-open-problem.md"),
                candidate,
                encoding);
            var bibkey = note.Split('\n')
                .First(static line => line.StartsWith("bibkey: ", StringComparison.Ordinal))
                ["bibkey: ".Length..];
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(root, "Library", "notes", bibkey + ".md"),
                note,
                encoding);
            foreach (var declaration in declarations)
            {
                var path = Path.GetFullPath(
                    Path.Combine(root, declaration.Replace('/', Path.DirectorySeparatorChar) + ".lean"));
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                TemporaryFileSystem.File.WriteAllText(path, "-- fixture\n", encoding);
            }
            foreach (var declaration in frozenDeclarations ?? [])
            {
                var path = Path.GetFullPath(Path.Combine(
                    root,
                    "Golden",
                    "Frozen",
                    "state",
                    declaration.Replace('/', Path.DirectorySeparatorChar) + ".lean.json"));
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                TemporaryFileSystem.File.WriteAllText(
                    path,
                    "{\"statement_id\":\"sha256:" + new string('d', 64) + "\"}\n",
                    encoding);
            }

            assertion(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    private static string Note(string bibkey, string doi) =>
        "---\n"
        + $"bibkey: {bibkey}\n"
        + "authors: Vera T. Sos\n"
        + "year: 1957\n"
        + "title: On the three gap theorem\n"
        + $"doi: {doi}\n"
        + "claim: Gap lengths for irrational rotations.\n"
        + "strata_touched: []\n"
        + "license: citation-only\n"
        + "triage: anchor\n"
        + "---\n";

    private static void WithCatalog(
        IReadOnlyDictionary<string, string> problems,
        Action<string> assertion)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-problems-" + Guid.NewGuid().ToString("N"));
        var directory = Path.Combine(root, "Problems");
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        try
        {
            foreach (var (name, content) in problems)
            {
                var path = Path.GetFullPath(Path.Combine(directory, name));
                TemporaryFileSystem.File.WriteAllText(path, content, new UTF8Encoding(false, true));
            }

            assertion(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    private static string WithoutFrontMatterKey(string document, string key)
    {
        var lines = document.Split('\n');
        var kept = lines.Where(line =>
            !line.StartsWith(key + ":", StringComparison.Ordinal)
            && !(string.Equals(key, "motivation_gids", StringComparison.Ordinal)
                && line.StartsWith("  - D5/", StringComparison.Ordinal)));
        return string.Join('\n', kept);
    }

    private static string WithoutSection(string document, string section)
    {
        var marker = "## " + section + "\n";
        var start = document.IndexOf(marker, StringComparison.Ordinal);
        var next = document.IndexOf("\n## ", start + marker.Length, StringComparison.Ordinal);
        return next < 0
            ? document[..start]
            : document[..start] + document[(next + 1)..];
    }

    private static string Candidate(
        string slug,
        string bibkey = "sos1957threegap",
        string arxivId = "2305.08349",
        string triage = "theorem",
        IReadOnlyList<string>? motivationGids = null)
    {
        var gids = motivationGids ?? ["D5/S1/Phase/Basic"];
        var chain = gids.Count == 0
            ? "motivation_gids: []\n"
            : "motivation_gids:\n"
                + string.Concat(gids.Select(static gid => $"  - {gid}\n"));
        return "---\n"
            + $"slug: {slug}\n"
            + $"bibkey: {bibkey}\n"
            + $"arxiv_id: {arxivId}\n"
            + $"triage: {triage}\n"
            + chain
            + "---\n"
            + "\n"
            + "# A sample open problem\n"
            + "\n"
            + "## Problem\n"
            + "\n"
            + "Prove the sample statement.\n"
            + "\n"
            + "## Motivation\n"
            + "\n"
            + "The frozen phase layer already supplies the gap lengths.\n"
            + "\n"
            + "## Gap\n"
            + "\n"
            + "No sample declaration exists yet.\n"
            + "\n"
            + "## Route\n"
            + "\n"
            + "Port the definition, then close the finite case.\n"
            + "\n"
            + "## Falsifier\n"
            + "\n"
            + "A concrete counterexample refutes it.\n"
            + "\n"
            + "## Evidence\n"
            + "\n"
            + "Enumerate the first thousand cases exactly.\n"
            + "\n"
            + "## Triage\n"
            + "\n"
            + "Reachable with the frozen phase layer.\n"
            + "\n"
            + "## ASSUMED-UNVERIFIED\n"
            + "\n"
            + "- Whether the problem was resolved after the cited version.\n";
    }
}
