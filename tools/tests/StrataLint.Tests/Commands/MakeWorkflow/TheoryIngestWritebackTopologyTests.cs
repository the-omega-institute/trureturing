using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed class TheoryIngestWritebackTopologyTests
{
    [Fact]
    public void TheoryIngestUsesOneReadOnlyTrustedPreparationAndOneMinimalWriteback()
    {
        var workflow = LoadWorkflow();
        var jobs = Mapping(workflow, "jobs");
        var prepare = Job(workflow, "trusted-prepare");
        var writeback = Job(workflow, "writeback");

        Assert.Equal(2, jobs.Children.Count);
        Assert.Equal("Prepare trusted theory ingest closure", Scalar(prepare, "name"));
        Assert.Equal("read", Scalar(Mapping(prepare, "permissions"), "contents"));
        Assert.Equal("Authorize and write back theory ingest closure", Scalar(writeback, "name"));
        Assert.Equal("write", Scalar(Mapping(writeback, "permissions"), "contents"));
        Assert.Equal("trusted-prepare", Scalar(writeback, "needs"));

        var prepareText = Render(prepare);
        Assert.DoesNotContain("${{ secrets.", prepareText, StringComparison.Ordinal);
        Assert.DoesNotContain("${{ github.token }}", prepareText, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.base.sha", prepareText, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.head.sha", prepareText, StringComparison.Ordinal);
        Assert.Contains("actions/upload-artifact@v4", prepareText, StringComparison.Ordinal);
        Assert.Contains("theory-ingest-trusted-closure", prepareText, StringComparison.Ordinal);
        Assert.Contains("trusted-artifact", prepareText, StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackJobDoesNotRunCanonicalProducers()
    {
        var workflow = LoadWorkflow();
        var writeback = Job(workflow, "writeback");
        var text = Render(writeback);

        Assert.DoesNotContain("make ingest", text, StringComparison.Ordinal);
        Assert.DoesNotContain("make lean-report", text, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet ", text, StringComparison.Ordinal);
        Assert.DoesNotContain("setup-dotnet", text, StringComparison.Ordinal);
        Assert.DoesNotContain("setup-lean", text, StringComparison.Ordinal);
        Assert.DoesNotContain("actions/cache", text, StringComparison.Ordinal);
        Assert.DoesNotContain("candidate-data", text, StringComparison.Ordinal);
        Assert.DoesNotContain("proposal", text, StringComparison.OrdinalIgnoreCase);

        var steps = Sequence(writeback, "steps").Children.OfType<YamlMappingNode>().ToArray();
        Assert.DoesNotContain(
            steps,
            static step => TryScalar(step, "uses", out var uses)
                && uses.StartsWith("./", StringComparison.Ordinal));
        Assert.DoesNotContain(
            steps,
            static step => TryScalar(step, "run", out _)
                && step.Children.ContainsKey(new YamlScalarNode("working-directory")));
        Assert.Contains(
            steps,
            static step => TryScalar(step, "uses", out var uses)
                && uses == "actions/download-artifact@v4");
        Assert.Contains(
            DescendantScalars(writeback),
            static value => value.Contains(
                "$GITHUB_WORKSPACE/trusted-validator/tools/scripts/workflow/theory-ingest-closure.sh",
                StringComparison.Ordinal));
    }

    [Fact]
    public void WritebackExecutionClosureDoesNotInvokeCanonicalProducers()
    {
        var writeback = Render(Job(LoadWorkflow(), "writeback"));
        var scriptFunctions = ShellFunctions(LoadScript() + "\n" + LoadGithubCasScript());
        var reachable = ReachableFunctions("writeback", scriptFunctions);
        var executionClosure = writeback + "\n" + string.Join(
            "\n",
            reachable.Select(name => scriptFunctions[name]));
        var producer = new Regex(
            @"(?im)\bmake\s+(?:-C\s+\S+\s+)?(?:ingest|lean-report)\b|\bdotnet\s+run\b[^\r\n]*\bStrataLint\b");

        Assert.DoesNotMatch(producer, executionClosure);
    }

    [Fact]
    public void TrustedPreparationDoesNotAuthorizeAnyCandidateProposal()
    {
        var workflow = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/theory-ingest.yml"));
        var script = LoadScript();

        Assert.DoesNotContain("propose:", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("theory-ingest-proposal", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("proposal/theory-ingest.patch", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("authorize_exact_patch", script, StringComparison.Ordinal);
        Assert.DoesNotContain("candidate proposal", script, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void TrustedPreparationFailsClosedWhenEventHeadChangesLeanReportInputClosure()
    {
        var prepare = Render(Job(LoadWorkflow(), "trusted-prepare"));
        var script = LoadScript();

        Assert.Contains("guard-inputs", prepare, StringComparison.Ordinal);
        Assert.Contains(
            "assert_report_input_closure_unchanged",
            script,
            StringComparison.Ordinal);
        Assert.Contains("\"$repository\" \"$candidate_data\" \"$fork_sha\" \"$head_sha\"", script, StringComparison.Ordinal);
        Assert.Contains("load_candidate_input_patterns", script, StringComparison.Ordinal);
        Assert.Contains("CANDIDATE_INPUT_PATHSPECS", script, StringComparison.Ordinal);
        Assert.Contains("consumed_by", script, StringComparison.Ordinal);
        Assert.Contains("IngestCommand", script, StringComparison.Ordinal);
        Assert.DoesNotContain("D5/*.lean|Trureturing.lean", script, StringComparison.Ordinal);
        Assert.Contains("split the theory-only PR", script, StringComparison.Ordinal);
    }

    [Fact]
    public void InvalidLeanReportCacheFallsBackToColdProduction()
    {
        var prepare = Job(LoadWorkflow(), "trusted-prepare");
        var steps = Sequence(prepare, "steps").Children.OfType<YamlMappingNode>().ToArray();
        var validation = Step(steps, "Validate restored trusted canonical Lean report");
        Assert.Equal("lean-report-cache-validation", Scalar(validation, "id"));
        Assert.Equal("true", Scalar(validation, "continue-on-error"));

        const string fallback = "steps.lean-report-cache-validation.outcome != 'success'";
        Assert.Equal(fallback, Scalar(Step(steps, "Restore elan and pinned Lean toolchain for cold production"), "if"));
        Assert.Equal(fallback, Scalar(Step(steps, "Install pinned Lean toolchain for cold production"), "if"));
        Assert.Equal(fallback, Scalar(Step(steps, "Restore trusted Lean dependency artifacts for cold production"), "if"));
        Assert.Equal(fallback, Scalar(Step(steps, "Restore trusted Lean build artifacts for cold production"), "if"));
        Assert.Equal(fallback, Scalar(Step(steps, "Produce trusted canonical Lean report from cold path"), "if"));
    }

    [Fact]
    public void WritebackAuthorizedPathsAreDerivedFromFileMap()
    {
        var script = LoadScript();

        Assert.Contains(
            "filemap-conform --producer-write-set IngestCommand",
            script,
            StringComparison.Ordinal);
        Assert.Contains("load_producer_write_patterns", script, StringComparison.Ordinal);
        Assert.Contains("load_pinned_write_patterns", script, StringComparison.Ordinal);
        Assert.Contains(
            "load_pinned_write_patterns \"$repository\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("produced_by", script, StringComparison.Ordinal);
        Assert.Contains("runtime_disposition", script, StringComparison.Ordinal);
        Assert.Contains("committed-", script, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/Digestion/atoms/**", script, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/Digestion/backfill/**", script, StringComparison.Ordinal);
        Assert.DoesNotContain("set_write_patterns \"Meta/Digestion/", script, StringComparison.Ordinal);
    }

    [Fact]
    public void TrustedArtifactEnvelopeBindsEveryAuthorityInputAndDigest()
    {
        var script = LoadScript();
        var expectedKeys = new[]
        {
            "base_sha",
            "head_sha",
            "patch_sha256",
            "report_input_address",
            "report_sha256",
            "theory_tree_sha",
        };

        foreach (var key in expectedKeys)
        {
            Assert.Contains($"\"{key}\"", script, StringComparison.Ordinal);
        }

        Assert.Contains("local digest_path=\"${envelope}.sha256\"", script, StringComparison.Ordinal);
        Assert.Contains("canonical envelope bytes", script, StringComparison.Ordinal);
        Assert.Contains("envelope digest", script, StringComparison.Ordinal);
        Assert.Contains("self-verification patch differs", script, StringComparison.Ordinal);
        Assert.Contains("self-verification report SHA differs", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackRejectsUnsafePatchShapesBeforeCommit()
    {
        var script = LoadScript();

        Assert.Contains("patch path is outside the FILEMAP-derived write set", script, StringComparison.Ordinal);
        Assert.Contains("delete, rename, copy, type change", script, StringComparison.Ordinal);
        Assert.Contains("symlink/submodule", script, StringComparison.Ordinal);
        Assert.Contains("binary patches are not authorized", script, StringComparison.Ordinal);
        Assert.Contains("validate_patch_into_index", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WriteTransactionUsesAtomicCompareAndSwapWithoutAnyForcePushForm()
    {
        var workflow = Render(Job(LoadWorkflow(), "writeback"));
        var script = LoadScript() + "\n" + LoadGithubCasScript();

        Assert.Contains("github.event.pull_request.head.sha", workflow, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.head.ref", workflow, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.head.repo.full_name", workflow, StringComparison.Ordinal);
        Assert.Contains("github.repository", workflow, StringComparison.Ordinal);
        Assert.Contains("github.token", workflow, StringComparison.Ordinal);
        Assert.Contains(
            "source \"$theory_ingest_script_directory/theory-ingest-github-cas.sh\"",
            LoadScript(),
            StringComparison.Ordinal);
        Assert.Contains("commit-tree \"$tree_sha\" -p \"$head_sha\"", script, StringComparison.Ordinal);
        Assert.Contains(
            "merge-base --is-ancestor \"$head_sha\" \"$commit_sha\"",
            script,
            StringComparison.Ordinal);
        Assert.Matches(
            new Regex(@"update-ref\s+\\?\s*""\$remote_ref""\s+""\$new_sha""\s+""\$expected_sha"""),
            script);
        Assert.Contains("UpdateRefsInput", script, StringComparison.Ordinal);
        Assert.Contains("\"beforeOid\": sys.argv[4]", script, StringComparison.Ordinal);
        Assert.Contains("\"afterOid\": sys.argv[5]", script, StringComparison.Ordinal);
        Assert.Contains("\"name\": sys.argv[3]", script, StringComparison.Ordinal);
        Assert.Contains("\"force\": False", script, StringComparison.Ordinal);
        Assert.Contains("remote head does not equal the committed writeback", script, StringComparison.Ordinal);
        Assert.Contains("remote head drifted from the event head", script, StringComparison.Ordinal);
        Assert.DoesNotContain("git -C \"$repository\" push", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--force-with-lease", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--force-if-includes", script, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateTheoryIsOnlyConsumedAsSparseRegularBlobData()
    {
        var prepare = Job(LoadWorkflow(), "trusted-prepare");
        var steps = Sequence(prepare, "steps").Children.OfType<YamlMappingNode>().ToArray();
        var candidateCheckout = Assert.Single(
            steps,
            static step => TryScalar(step, "id", out var id) && id == "checkout-candidate-data");
        var with = Mapping(candidateCheckout, "with");
        Assert.Equal("docs/develop/theory", Scalar(with, "sparse-checkout"));
        Assert.Equal("false", Scalar(with, "persist-credentials"));

        var scripts = steps
            .Where(static step => TryScalar(step, "run", out _))
            .Select(static step => Scalar(step, "run"));
        Assert.DoesNotContain(
            scripts,
            static script => script.Contains("candidate-data/tools/", StringComparison.Ordinal)
                || script.Contains("$GITHUB_WORKSPACE/candidate-data/", StringComparison.Ordinal));
        Assert.Contains("assert_candidate_theory_is_regular_data", LoadScript(), StringComparison.Ordinal);
    }

    private static YamlMappingNode LoadWorkflow()
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/theory-ingest.yml"))));
        return Assert.IsType<YamlMappingNode>(Assert.Single(stream.Documents).RootNode);
    }

    private static string LoadScript() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/scripts/workflow/theory-ingest-closure.sh"));

    private static string LoadGithubCasScript() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/scripts/workflow/theory-ingest-github-cas.sh"));

    private static YamlMappingNode Step(IEnumerable<YamlMappingNode> steps, string name) =>
        Assert.Single(steps, step => TryScalar(step, "name", out var actual) && actual == name);

    private static IReadOnlyDictionary<string, string> ShellFunctions(string script)
    {
        var functions = new Dictionary<string, string>(StringComparer.Ordinal);
        var lines = script.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n');
        var declaration = new Regex(@"^([a-z][a-z0-9_]*)\(\) \{$");
        var heredoc = new Regex(@"<<-?'?([A-Z][A-Z0-9_]*)'?");
        for (var index = 0; index < lines.Length; index++)
        {
            var match = declaration.Match(lines[index]);
            if (!match.Success) continue;
            var body = new List<string>();
            string? heredocEnd = null;
            for (index++; index < lines.Length; index++)
            {
                var line = lines[index];
                if (heredocEnd is not null)
                {
                    body.Add(line);
                    if (line == heredocEnd) heredocEnd = null;
                    continue;
                }

                var heredocMatch = heredoc.Match(line);
                if (heredocMatch.Success) heredocEnd = heredocMatch.Groups[1].Value;
                if (line == "}") break;
                body.Add(line);
            }

            functions.Add(match.Groups[1].Value, string.Join('\n', body));
        }

        return functions;
    }

    private static IReadOnlySet<string> ReachableFunctions(
        string entrypoint,
        IReadOnlyDictionary<string, string> functions)
    {
        var reachable = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>();
        pending.Push(entrypoint);
        while (pending.TryPop(out var name))
        {
            Assert.True(functions.ContainsKey(name), $"shell function is absent: {name}");
            if (!reachable.Add(name)) continue;
            var body = functions[name];
            foreach (var candidate in functions.Keys)
            {
                if (!reachable.Contains(candidate)
                    && Regex.IsMatch(
                        body,
                        $@"(?m)(?:^[ \t]*(?:(?:if|elif|while|until)[ \t]+!?[ \t]*)?|[;&|][ \t]*|\$\([ \t]*){Regex.Escape(candidate)}(?=[ \t>""'$()\\]|$)"))
                {
                    pending.Push(candidate);
                }
            }
        }

        return reachable;
    }

    private static YamlMappingNode Job(YamlMappingNode workflow, string name) =>
        Mapping(Mapping(workflow, "jobs"), name);

    private static YamlMappingNode Mapping(YamlMappingNode node, string key) =>
        Assert.IsType<YamlMappingNode>(node.Children[new YamlScalarNode(key)]);

    private static YamlSequenceNode Sequence(YamlMappingNode node, string key) =>
        Assert.IsType<YamlSequenceNode>(node.Children[new YamlScalarNode(key)]);

    private static string Scalar(YamlMappingNode node, string key) =>
        Assert.IsType<YamlScalarNode>(node.Children[new YamlScalarNode(key)]).Value ?? string.Empty;

    private static bool TryScalar(YamlMappingNode node, string key, out string value)
    {
        if (node.Children.TryGetValue(new YamlScalarNode(key), out var child)
            && child is YamlScalarNode { Value: { } scalar })
        {
            value = scalar;
            return true;
        }

        value = string.Empty;
        return false;
    }

    private static IEnumerable<string> DescendantScalars(YamlNode node) => node switch
    {
        YamlScalarNode { Value: { } value } => [value],
        YamlSequenceNode sequence => sequence.Children.SelectMany(DescendantScalars),
        YamlMappingNode mapping => mapping.Children
            .SelectMany(static pair => DescendantScalars(pair.Key).Concat(DescendantScalars(pair.Value))),
        _ => [],
    };

    private static string Render(YamlNode node)
    {
        var stream = new YamlStream(new YamlDocument(node));
        using var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        stream.Save(writer, assignAnchors: false);
        return writer.ToString();
    }
}
