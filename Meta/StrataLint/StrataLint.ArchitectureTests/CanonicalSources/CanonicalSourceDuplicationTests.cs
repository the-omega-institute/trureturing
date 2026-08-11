using System.Diagnostics;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CanonicalSourceDuplicationTests
{
    [Fact]
    public void RepositoryCSharpDoesNotCopyCanonicalTicketMappingsOrAtomizerIds()
    {
        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Fact]
    public void LedgerAtomizerIdLiteralIsRejectedByTheRedFixture()
    {
        const string id = "synthetic-v1";
        const string source = "const string copied = \"\"\"\\natomizer: synthetic-v1\\n\"\"\";";

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectAtomizerIdLiterals(
            "Meta/StrataLint/Synthetic.cs",
            source,
            [id]));

        Assert.Contains("AtomizerRegistry", finding.Message, StringComparison.Ordinal);
    }

    // 边界语义由 ContainsWholeToken 承担(此前是内插正则的前后瞻)。这三条把它钉住,
    // 使那次「正则换扫描」不是靠肉眼比对而是靠机器判等。
    [Theory]
    [InlineData("var x = \"synthetic-v1\";", true)]                    // 整词
    [InlineData("var x = \"atomizer: synthetic-v1 end\";", true)]      // 两侧皆非 token 字符
    [InlineData("var x = \"presynthetic-v1\";", false)]                // 左侧粘连字母
    [InlineData("var x = \"synthetic-v10\";", false)]                  // 右侧粘连数字
    [InlineData("var x = \"synthetic-v1.beta\";", false)]              // 右侧粘连点
    [InlineData("var x = \"a-synthetic-v1\";", false)]                 // 左侧粘连连字符
    [InlineData("var x = \"xsynthetic-v1 and synthetic-v1\";", true)]  // 先粘连后整词:须继续搜完
    public void AtomizerIdLiteralMatchesOnlyOnWholeTokenBoundaries(string source, bool expectFinding)
    {
        var findings = CanonicalSourceDuplicationPolicy.InspectAtomizerIdLiterals(
            "Meta/StrataLint/Synthetic.cs",
            source,
            ["synthetic-v1"]);

        Assert.Equal(expectFinding, findings.Count > 0);
    }

    [Fact]
    public void RegistryOwnsItsAtomizerIdLiterals()
    {
        const string id = "synthetic-v1";
        const string source = "var registered = \"synthetic-v1\";";

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectAtomizerIdLiterals(
            CanonicalSourceDuplicationPolicy.AtomizerRegistryPath,
            source,
            [id]));
    }

    [Theory]
    [InlineData("Meta/StrataLint/Synthetic.cs")]
    [InlineData("Golden/cases/synthetic.toml")]
    public void LongExactSpecificationPassageIsRejectedByTheRedFixture(string path)
    {
        const string passage =
            "这是一段足够长的合成规范原文，用于证明机器能够识别可变真源被逐字复制到判例装置中的情形，并且不会依赖真实项目规范的任何具体主张或编号。";
        var specification = "# Synthetic specification\n\n" + passage + "\n";
        var source = "fixture = \"" + passage + "\"\n";

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectSpecificationCopies(
            path,
            source,
            specification));

        Assert.Contains("specification", finding.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ShortOrRewrittenSpecificationTextIsNotRejected()
    {
        const string specification =
            "短语不构成长段复制。这个合成句子足够长，但下游只保留语义等价的重新表述，因此不应被精确匹配守卫拒绝。";
        const string source = "const string fixture = \"短语不构成长段复制\";";

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectSpecificationCopies(
            "Meta/StrataLint/Synthetic.cs",
            source,
            specification));
    }

    [Fact]
    public void LongExactBlueprintPassageIsRejectedByTheRedFixture()
    {
        const string blueprint = """
            var document = Paragraph(Text(
                "The synthetic Blueprint records an authored explanation whose exact wording " +
                "belongs only in the canonical document source and nowhere else."));
            """;
        const string source = """
            Assert.Contains(
                "The synthetic Blueprint records an authored explanation whose exact wording belongs only in the canonical document source and nowhere else.",
                rendered,
                StringComparison.Ordinal);
            """;

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectBlueprintCopies(
            "Meta/StrataLint/SyntheticTests.cs",
            source,
            [("Blueprint/D5/S0/Synthetic.scribe.cs", blueprint)]));

        Assert.Contains(
            "Blueprint/D5/S0/Synthetic.scribe.cs",
            finding.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShortOrRewrittenBlueprintTextIsNotRejected()
    {
        const string blueprint = """
            var document = Blocks(
                Paragraph(Text("An exact Blueprint phrase stays short.")),
                Paragraph(Text(
                    "The synthetic Blueprint records an authored explanation whose exact wording " +
                    "belongs only in the canonical document source and nowhere else.")));
            """;
        const string source = """
            const string shortCopy = "An exact Blueprint phrase stays short.";
            const string rewritten =
                "This independently written explanation resembles the canonical document's meaning, " +
                "but it deliberately uses different words and therefore is not a verbatim copy.";
            const string identifier = "D5/S0/Synthetic.synthetic_declaration";
            const string latex = @"\operatorname{Synthetic}(x) = x";
            """;

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectBlueprintCopies(
            "Meta/StrataLint/SyntheticTests.cs",
            source,
            [("Blueprint/D5/S0/Synthetic.scribe.cs", blueprint)]));
    }

    [Fact]
    public void RepositoryScanIncludesCSharpOutsideTheHarnessTree()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-canonical-source-" + Guid.NewGuid().ToString("N"));
        try
        {
            Directory.CreateDirectory(root);
            Git(root, "init", "--initial-branch=dev");
            Directory.CreateDirectory(Path.Combine(root, "Meta", "StrataLint"));
            File.WriteAllText(
                Path.Combine(root, "Meta", "BACKFILL.yaml"),
                "schema_version: 3\nledger: theory-digestion-v1\nsources: []\n"
                + "ticket_index:\n  - case_id: SYNTHETIC-CASE\n    gid: synthetic/gid\n");
            var repositoryRoot = RepositoryLayout.FindRoot();
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "registry.yaml"),
                Path.Combine(root, "Meta", "registry.yaml"));
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "domains.yaml"),
                Path.Combine(root, "Meta", "domains.yaml"));
            var specificationPath = Path.Combine(root, BootstrapGate.SpecificationPath);
            Directory.CreateDirectory(Path.GetDirectoryName(specificationPath)!);
            File.WriteAllText(specificationPath, "# Synthetic specification\n");
            var blueprint = Path.Combine(root, "Blueprint");
            Directory.CreateDirectory(blueprint);
            File.WriteAllText(
                Path.Combine(blueprint, "Synthetic.scribe.cs"),
                "var copied = new Dictionary<string, string> { [\"synthetic/gid\"] = \"SYNTHETIC-CASE\" };\n");
            Git(root, "add", "--", ".");

            var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectRepository(root));

            Assert.Equal("Blueprint/Synthetic.scribe.cs", finding.Path);
        }
        finally
        {
            if (Directory.Exists(root))
            {
                Directory.Delete(root, recursive: true);
            }
        }
    }

    private static void Git(string repositoryRoot, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = repositoryRoot,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(
            process.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {process.ExitCode}: {error}");
    }

    [Theory]
    [InlineData("[\"synthetic/gid\"] = \"SYNTHETIC-CASE\"")]
    [InlineData("[\"synthetic/gid\"] = [\"SYNTHETIC-CASE\"]")]
    [InlineData("[\"synthetic/gid\"] = new[] { \"SYNTHETIC-CASE\" }")]
    public void CanonicalTicketDictionaryEntryIsRejectedByTheRedFixture(string entry)
    {
        var source = $$"""
            var copied = new Dictionary<string, object>
            {
                {{entry}},
            };
            """;
        var tickets = new[]
        {
            (CaseId: "SYNTHETIC-CASE", Gid: "synthetic/gid"),
        };

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            tickets));

        Assert.Contains("Meta/BACKFILL.yaml", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SeparateDiagnosticLiteralsAreNotTreatedAsATicketMap()
    {
        const string source = """
            const string diagnostic = "SYNTHETIC-CASE";
            const string path = "synthetic/gid";
            """;
        var tickets = new[]
        {
            (CaseId: "SYNTHETIC-CASE", Gid: "synthetic/gid"),
        };

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            tickets));
    }

    [Theory]
    [InlineData("S0")]
    [InlineData("S4")]
    public void RegisteredDomainDictionaryEntryIsRejectedByTheRedFixture(string stratum)
    {
        var source = $$"""
            var copied = new Dictionary<string, string>
            {
                ["Carrier"] = "{{stratum}}",
            };
            """;
        var domains = new[]
        {
            (Name: "Carrier", Stratum: "S0"),
        };

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectDomainMappings(
            "Meta/StrataLint/Synthetic.cs",
            source,
            domains));

        Assert.Contains("Meta/domains.yaml", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SeparateDomainAndStratumLiteralsAreNotTreatedAsADomainMap()
    {
        const string source = """
            const string domain = "Carrier";
            const string stratum = "S0";
            """;
        var domains = new[]
        {
            (Name: "Carrier", Stratum: "S0"),
        };

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectDomainMappings(
            "Meta/StrataLint/Synthetic.cs",
            source,
            domains));
    }
}
