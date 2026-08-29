using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// The Lean build archive published to GitHub Releases is consumed as compiled .olean input,
/// so whoever can publish it sits underneath admission. Three seats reading independently
/// (#2729) established that a job-internal ref check is not a machine boundary: `gh workflow
/// run --ref` selects the workflow version from that branch, so a non-base version can delete
/// its own check. The boundary has to be the trigger set itself.
///
/// This pins the closure rather than any single file: the two explicitly authorized writers
/// are the scheduled Lean cache publisher and the protected-dev truth-release publisher. A third
/// writable workflow, or an unapproved trigger added to either one, turns this red instead of
/// relying on a reviewer remembering why it mattered.
/// </summary>
public sealed class ContentsWriteWorkflowClosureTests
{
    private static readonly string RepositoryRoot = RepositoryLayout.FindRoot();

    private static readonly IReadOnlyList<WorkflowSource> Workflows =
        GitIndexRepositoryFiles.Enumerate(RepositoryRoot)
            .Where(static file => file.RelativePath.StartsWith(".github/workflows/", StringComparison.Ordinal)
                && (file.RelativePath.EndsWith(".yml", StringComparison.Ordinal)
                    || file.RelativePath.EndsWith(".yaml", StringComparison.Ordinal)))
            .OrderBy(static file => file.RelativePath, StringComparer.Ordinal)
            .Select(static file => new WorkflowSource(file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();

    private const string ArchivePublisher = ".github/workflows/lean-cache-publish.yml";
    private const string TruthReleasePublisher = RepositoryPathPolicy.TruthReleasePublicationWorkflowPath;

    private static readonly IReadOnlySet<string> PublicationWriteScopes =
        new HashSet<string>(["contents", "packages", "id-token", "attestations"], StringComparer.Ordinal);

    [Fact]
    public void OnlyTheAuthorizedPublishersMayWriteRepositoryContents()
    {
        var writers = Workflows
            .Where(static source => DeclaresContentsWrite(source.Content))
            .Select(static source => source.Path)
            .ToArray();

        Assert.Equal([ArchivePublisher, TruthReleasePublisher], writers);
    }

    [Fact]
    public void TheArchivePublisherRunsOnlyOnASchedule()
    {
        var publisher = Workflows.SingleOrDefault(static source => source.Path == ArchivePublisher);
        Assert.NotNull(publisher);

        Assert.Equal(["schedule"], TriggerNames(publisher.Content));
    }

    [Fact]
    public void TheTruthReleasePublisherRunsOnlyOnScheduleOrRepositoryDispatch()
    {
        var publisher = Workflows.SingleOrDefault(static source => source.Path == TruthReleasePublisher);
        Assert.NotNull(publisher);

        // schedule + repository_dispatch only. workflow_dispatch is forbidden: GitHub's dispatch
        // `ref` selector would let a caller run a modified workflow definition (holding publication
        // write credentials) from an arbitrary ref. repository_dispatch has no ref selector — it
        // always runs the DEFAULT-branch workflow definition and carries no source_commit input —
        // so it cannot execute attacker-modified workflow text or select an arbitrary commit; the
        // produce job still walk-backs to the newest gate-verified protected-dev commit.
        // TriggerNames sorts ordinally, so the expected order is alphabetical.
        Assert.Equal(["repository_dispatch", "schedule"], TriggerNames(publisher.Content));
        Assert.Contains("cron: '17 * * * *'", publisher.Content, StringComparison.Ordinal);
        Assert.Contains("types: [publish-truth-release]", publisher.Content, StringComparison.Ordinal);
        Assert.DoesNotContain("workflow_dispatch", publisher.Content, StringComparison.Ordinal);
        // The repository_dispatch payload must never influence source selection: the produce
        // job resolves the protected dev tip and walk-backs to a gate-verified commit, so the
        // workflow must not read the caller-supplied client_payload or any dispatch inputs.
        Assert.DoesNotContain("client_payload", publisher.Content, StringComparison.Ordinal);
        Assert.DoesNotContain("github.event.inputs", publisher.Content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherDerivesTrustOnlyFromTheProtectedDevTip()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.Contains("repos/${GITHUB_REPOSITORY}/branches/dev", content, StringComparison.Ordinal);
        Assert.Contains(".protected", content, StringComparison.Ordinal);
        // #4006 briefly pinned the candidate to GITHUB_SHA and dropped the walk-back; #4010
        // restored the walk-back and now verifies provenance against GITHUB_SHA separately.
        // What must hold across both is unchanged: a candidate only becomes source_commit after
        // it is shape-checked as a commit sha and every required check on it reports success.
        Assert.Contains(
            "repos/${GITHUB_REPOSITORY}/commits?sha=dev&per_page=40",
            content,
            StringComparison.Ordinal);
        Assert.Contains(
            "[[ \"$candidate\" =~ ^[0-9a-f]{40}$ ]] || continue",
            content,
            StringComparison.Ordinal);
        Assert.Contains(
            "[[ \"$candidate_green\" == true ]]",
            content,
            StringComparison.Ordinal);
        Assert.Contains("check-runs?per_page=100", content, StringComparison.Ordinal);
        Assert.Contains("publish_ready=false", content, StringComparison.Ordinal);
        Assert.Contains("git symbolic-ref -q HEAD", content, StringComparison.Ordinal);
        Assert.Contains(
            "REQUIRED_CHECKS: 'Candidate harness engineering checks|Canonical Lean report production|Content-addressed dev baseline admission'",
            content,
            StringComparison.Ordinal);
        Assert.Contains(".merge_base_commit.sha", content, StringComparison.Ordinal);
        Assert.Contains("commit_on_protected_dev=true", content, StringComparison.Ordinal);
        Assert.Contains("--commit-on-protected-dev \"$COMMIT_ON_PROTECTED_DEV\"", content, StringComparison.Ordinal);
        Assert.DoesNotContain("--commit-on-protected-dev true", content, StringComparison.Ordinal);
        Assert.Contains("COMMIT_ON_PROTECTED_DEV: ${{ steps.identity.outputs.commit_on_protected_dev }}", content, StringComparison.Ordinal);
        Assert.Contains("git show -s --format=%ct HEAD", content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherSerializesAndBindsImmutableDigestPublications()
    {
        var root = WorkflowRoot(TruthReleaseWorkflow());
        var content = TruthReleaseWorkflow().Content;
        var concurrency = Assert.IsType<YamlMappingNode>(MappingValue(root, "concurrency"));

        Assert.Equal("truth-release-publish-dev", Assert.IsType<YamlScalarNode>(MappingValue(concurrency, "group")).Value);
        Assert.Equal("false", Assert.IsType<YamlScalarNode>(MappingValue(concurrency, "cancel-in-progress")).Value);
        Assert.False(TryMappingValue(Job(root, "publish"), "concurrency", out _));
        Assert.Contains("produced_at=\"$(date -u --date=\"@${commit_epoch}\"", content, StringComparison.Ordinal);
        Assert.Contains("--sort=name", content, StringComparison.Ordinal);
        Assert.Contains("gzip -n", content, StringComparison.Ordinal);
        Assert.Contains("oras pull \"$reference\"", content, StringComparison.Ordinal);
        Assert.Contains("cmp -s \"$ARCHIVE\"", content, StringComparison.Ordinal);
        Assert.Contains("immutable_reference=\"$OCI_REPOSITORY@$oci_digest\"", content, StringComparison.Ordinal);
        Assert.Contains("verify_pinned_oci_artifact \"$immutable_reference\"", content, StringComparison.Ordinal);
        Assert.Contains("[[ \"${reference##*@}\" =~ ^sha256:[0-9a-f]{64}$ ]]", content, StringComparison.Ordinal);
        Assert.Contains("reference=%s\\n' \"$immutable_reference\"", content, StringComparison.Ordinal);
        Assert.Contains("OCI lookup failed without a definitive not-found response", content, StringComparison.Ordinal);
        Assert.Contains("OCI digest tag moved during immutable verification", content, StringComparison.Ordinal);
        Assert.Contains(
            "source_url=\"https://github.com/${GITHUB_REPOSITORY}/commit/${SOURCE_COMMIT}\"",
            content,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "org.opencontainers.image.source=https://github.com/${GITHUB_REPOSITORY}/commit/${GITHUB_SHA}",
            content,
            StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleaseProducerCannotPublishOrMintOidcCredentials()
    {
        var root = WorkflowRoot(TruthReleaseWorkflow());

        Assert.Empty(Permissions(root));
        Assert.Equal(
            new Dictionary<string, string>(StringComparer.Ordinal) { ["contents"] = "read" },
            Permissions(Job(root, "produce")));
        Assert.Equal(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["contents"] = "write",
                ["packages"] = "write",
                ["id-token"] = "write",
                ["attestations"] = "write",
            },
            Permissions(Job(root, "publish")));
    }

    [Fact]
    public void NoTruthReleaseJobMaterializesOrExecutesRepositorySourceWithPublicationWriteAuthority() =>
        AssertWriteJobsAreRepositorySourceIsolated(TruthReleaseWorkflow());

    [Fact]
    public void AHostileWriteJobThatRunsDotnetMakesTheClosureGuardRed()
    {
        const string hostileWorkflow = """
            permissions: {}
            jobs:
              producer:
                permissions:
                  contents: read
                steps:
                  - run: dotnet test harmless.csproj
              hostile:
                permissions:
                  contents: write
                steps:
                  - name: Execute repository code while holding write authority
                    run: dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj
                  - run: lake build
                  - run: make lean-report
            """;

        var failure = Record.Exception(() =>
            AssertWriteJobsAreRepositorySourceIsolated(new WorkflowSource("hostile-fixture.yml", hostileWorkflow)));

        Assert.NotNull(failure);
        Assert.Contains(
            "Jobs with publication/OIDC write authority may not execute repository code: hostile",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AHostileWriteJobThatCallsALocalReusableWorkflowMakesTheClosureGuardRed()
    {
        const string hostileWorkflow = """
            permissions: {}
            jobs:
              hostile:
                permissions:
                  contents: write
                steps:
                  - name: Execute a local reusable workflow while holding write authority
                    uses: ./.github/workflows/anything.yml
            """;

        var failure = Record.Exception(() =>
            AssertWriteJobsAreRepositorySourceIsolated(new WorkflowSource("hostile-local-workflow.yml", hostileWorkflow)));

        Assert.NotNull(failure);
        Assert.Contains(
            "Jobs with publication/OIDC write authority may not materialize repository source: hostile",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AHostileWriteJobThatChecksOutRepositorySourceMakesTheClosureGuardRed()
    {
        const string hostileWorkflow = """
            permissions: {}
            jobs:
              hostile:
                permissions:
                  id-token: write
                steps:
                  - name: Materialize repository source while holding OIDC authority
                    uses: actions/checkout@v4
            """;

        var failure = Record.Exception(() =>
            AssertWriteJobsAreRepositorySourceIsolated(new WorkflowSource("hostile-checkout.yml", hostileWorkflow)));

        Assert.NotNull(failure);
        Assert.Contains(
            "Jobs with publication/OIDC write authority may not materialize repository source: hostile",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AHostileWriteJobThatCallsSelfRepositorySourceMakesTheClosureGuardRed()
    {
        const string hostileWorkflow = """
            permissions: {}
            jobs:
              hostile:
                permissions:
                  attestations: write
                steps:
                  - name: Materialize a self-repository action while holding write authority
                    uses: the-omega-institute/trureturing/publish/action@dev
            """;

        var failure = Record.Exception(() =>
            AssertWriteJobsAreRepositorySourceIsolated(new WorkflowSource("hostile-self-source.yml", hostileWorkflow)));

        Assert.NotNull(failure);
        Assert.Contains(
            "Jobs with publication/OIDC write authority may not materialize repository source: hostile",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AHostileWriteJobThatRunsARepositoryScriptMakesTheClosureGuardRed()
    {
        const string hostileWorkflow = """
            permissions: {}
            jobs:
              hostile:
                permissions:
                  packages: write
                steps:
                  - name: Execute a repository script while holding write authority
                    run: bash scripts/publish.sh
            """;

        var failure = Record.Exception(() =>
            AssertWriteJobsAreRepositorySourceIsolated(new WorkflowSource("hostile-script.yml", hostileWorkflow)));

        Assert.NotNull(failure);
        Assert.Contains(
            "Jobs with publication/OIDC write authority may not execute repository code: hostile",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherConsumesOnlyTheRunBoundTransfer()
    {
        var content = TruthReleaseWorkflow().Content;
        var publisherScalars = ScalarValues(Job(WorkflowRoot(TruthReleaseWorkflow()), "publish"));

        Assert.Contains("artifact-ids: ${{ needs.produce.outputs.artifact_id }}", content, StringComparison.Ordinal);
        Assert.Contains("truth-release-transfer.v1", content, StringComparison.Ordinal);
        Assert.Contains(".run_id == $ENV.GITHUB_RUN_ID", content, StringComparison.Ordinal);
        Assert.Contains(".run_attempt == $ENV.PRODUCE_RUN_ATTEMPT", content, StringComparison.Ordinal);
        Assert.Contains(".release_digest == $ENV.RELEASE_DIGEST", content, StringComparison.Ordinal);
        Assert.Contains("retention-days: 7", content, StringComparison.Ordinal);
        Assert.Contains("Re-run failed jobs", content, StringComparison.Ordinal);
        Assert.Contains("full re-run", content, StringComparison.Ordinal);
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("actions/checkout", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("actions/setup-dotnet", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("dotnet ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("lake ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("make ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("tools/", StringComparison.Ordinal));
    }

    [Fact]
    public void TheTruthReleasePublisherRepairsAndVerifiesProvenanceOnEveryRun()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.DoesNotContain("steps.oci.outputs.pushed", content, StringComparison.Ordinal);
        Assert.Contains("attestations/${encoded_digest}", content, StringComparison.Ordinal);
        Assert.Contains("gh attestation verify \"oci://${SUBJECT_REFERENCE}\"", content, StringComparison.Ordinal);
        Assert.Contains("SUBJECT_REFERENCE: ${{ steps.oci.outputs.reference }}", content, StringComparison.Ordinal);
        Assert.Contains("subject-digest: ${{ steps.oci.outputs.digest }}", content, StringComparison.Ordinal);
        Assert.Contains("--signer-workflow \"$GITHUB_REPOSITORY/.github/workflows/truth-release-publish.yml\"", content, StringComparison.Ordinal);
        // #4010: the provenance verify gate binds to GITHUB_SHA, which attests publisher-run
        // authenticity - attest-build-provenance can only stamp GITHUB_SHA. It is deliberately
        // not the source-of-truth for the bundle's source commit; that travels in the
        // integrity-bound manifest and the consumer re-derives it. So the digest verified here
        // is the run's own commit, and the walk-back source_commit need not equal it.
        Assert.Contains("--source-digest \"$GITHUB_SHA\"", content, StringComparison.Ordinal);
        Assert.DoesNotContain("--source-digest \"$SOURCE_COMMIT\"", content, StringComparison.Ordinal);
        Assert.Contains("--source-ref 'refs/heads/dev'", content, StringComparison.Ordinal);
        Assert.Contains("GHCR provenance did not become verifiable", content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherCreatesAndRepairsOneImmutableRelease()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.Contains("gh release create", content, StringComparison.Ordinal);
        Assert.Contains("gh release upload", content, StringComparison.Ordinal);
        Assert.Contains("gh release download", content, StringComparison.Ordinal);
        Assert.Contains("cmp -s \"$asset\" \"$verify_dir/$name\"", content, StringComparison.Ordinal);
        Assert.Contains("count=\"$(jq --arg name", content, StringComparison.Ordinal);
        Assert.Contains("(.assets | length) == ($expected | length)", content, StringComparison.Ordinal);
        Assert.Contains("([.assets[].name] | sort) == $expected", content, StringComparison.Ordinal);
        Assert.Contains("source commit is no longer an ancestor of protected dev before GitHub Release publication", content, StringComparison.Ordinal);
        Assert.Contains("verify_protected_dev_tip\n            if gh release create", content, StringComparison.Ordinal);
        Assert.Contains("verify_protected_dev_tip\n              gh release upload", content, StringComparison.Ordinal);
        Assert.Contains("assets=verified", content, StringComparison.Ordinal);
        Assert.DoesNotContain("release_collection_api=", content, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryWorkflowDeclaresItsTriggersAndPermissionsExplicitly()
    {
        // A workflow with no `permissions:` block inherits the repository default, which is
        // configured outside this repository and can therefore grant write without any diff
        // here. Reading the closure only works if every member declares what it takes.
        var undeclared = Workflows
            .Where(static source => !DeclaresAnyContentsPermission(source.Content)
                || TriggerNames(source.Content).Count == 0)
            .Select(static source => source.Path)
            .ToArray();

        Assert.Empty(undeclared);
    }

    private static bool DeclaresContentsWrite(string content) =>
        ContentsValues(content).Contains("write", StringComparer.Ordinal);

    private static WorkflowSource TruthReleaseWorkflow() =>
        Workflows.Single(static source => source.Path == TruthReleasePublisher);

    private static YamlMappingNode WorkflowRoot(WorkflowSource workflow) =>
        Assert.IsType<YamlMappingNode>(Assert.Single(Documents(workflow.Content)));

    private static YamlMappingNode Job(YamlMappingNode root, string name)
    {
        var jobs = Assert.IsType<YamlMappingNode>(MappingValue(root, "jobs"));
        return Assert.IsType<YamlMappingNode>(MappingValue(jobs, name));
    }

    private static void AssertWriteJobsAreRepositorySourceIsolated(WorkflowSource workflow)
    {
        var root = WorkflowRoot(workflow);
        var authoritativeJobs = Jobs(root)
            .Where(pair => HoldsPublicationWriteScope(root, pair.Value))
            .ToArray();
        var materializers = authoritativeJobs
            .Where(static pair => MaterializesRepositorySource(pair.Value))
            .Select(static pair => pair.Key)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var executors = authoritativeJobs
            .Where(static pair => ExecutesRepositoryCode(pair.Value))
            .Select(static pair => pair.Key)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.True(
            materializers.Length == 0,
            $"Jobs with publication/OIDC write authority may not materialize repository source: {string.Join(", ", materializers)}");
        Assert.True(
            executors.Length == 0,
            $"Jobs with publication/OIDC write authority may not execute repository code: {string.Join(", ", executors)}");
    }

    private static IReadOnlyDictionary<string, YamlMappingNode> Jobs(YamlMappingNode root)
    {
        var jobs = Assert.IsType<YamlMappingNode>(MappingValue(root, "jobs"));
        return jobs.Children.ToDictionary(
            static pair => Assert.IsType<YamlScalarNode>(pair.Key).Value ?? string.Empty,
            static pair => Assert.IsType<YamlMappingNode>(pair.Value),
            StringComparer.Ordinal);
    }

    private static bool HoldsPublicationWriteScope(YamlMappingNode root, YamlMappingNode job)
    {
        var permissions = TryMappingValue(job, "permissions", out var jobPermissions)
            ? jobPermissions
            : TryMappingValue(root, "permissions", out var workflowPermissions)
                ? workflowPermissions
                : null;

        return permissions switch
        {
            YamlScalarNode { Value: "write-all" } => true,
            YamlMappingNode mapping => mapping.Children.Any(pair =>
                pair.Key is YamlScalarNode { Value: { } name }
                && PublicationWriteScopes.Contains(name)
                && pair.Value is YamlScalarNode { Value: "write" }),
            _ => false,
        };
    }

    private static bool ExecutesRepositoryCode(YamlMappingNode job)
    {
        if (!TryMappingValue(job, "steps", out var stepsNode)
            || stepsNode is not YamlSequenceNode steps)
        {
            return false;
        }

        return steps.Children.OfType<YamlMappingNode>().Any(step =>
            TryMappingValue(step, "run", out var run)
                && run is YamlScalarNode { Value: { } command }
                && RepositoryPathPolicy.ContainsRepositorySourceExecutionIndicator(command));
    }

    private static bool MaterializesRepositorySource(YamlMappingNode job)
    {
        if (TryMappingValue(job, "uses", out var reusableWorkflow)
            && reusableWorkflow is YamlScalarNode { Value: { } workflow }
            && RepositoryPathPolicy.ContainsRepositorySourceMaterializationIndicator(workflow))
        {
            return true;
        }

        if (!TryMappingValue(job, "steps", out var stepsNode)
            || stepsNode is not YamlSequenceNode steps)
        {
            return false;
        }

        return steps.Children.OfType<YamlMappingNode>().Any(step =>
            (TryMappingValue(step, "uses", out var uses)
                && uses is YamlScalarNode { Value: { } action }
                && RepositoryPathPolicy.ContainsRepositorySourceMaterializationIndicator(action))
            || (TryMappingValue(step, "run", out var run)
                && run is YamlScalarNode { Value: { } command }
                && RepositoryPathPolicy.ContainsRepositorySourceMaterializationIndicator(command)));
    }

    private static IReadOnlyDictionary<string, string> Permissions(YamlMappingNode mapping)
    {
        var permissions = Assert.IsType<YamlMappingNode>(MappingValue(mapping, "permissions"));
        return permissions.Children
            .ToDictionary(
                static pair => Assert.IsType<YamlScalarNode>(pair.Key).Value ?? string.Empty,
                static pair => Assert.IsType<YamlScalarNode>(pair.Value).Value ?? string.Empty,
                StringComparer.Ordinal);
    }

    private static YamlNode MappingValue(YamlMappingNode mapping, string key) =>
        mapping.Children.Single(pair =>
            pair.Key is YamlScalarNode scalar && string.Equals(scalar.Value, key, StringComparison.Ordinal)).Value;

    private static bool TryMappingValue(YamlMappingNode mapping, string key, out YamlNode value)
    {
        foreach (var pair in mapping.Children)
        {
            if (pair.Key is YamlScalarNode scalar
                && string.Equals(scalar.Value, key, StringComparison.Ordinal))
            {
                value = pair.Value;
                return true;
            }
        }

        value = null!;
        return false;
    }

    private static IReadOnlyList<string> ScalarValues(YamlNode root)
    {
        var values = new List<string>();
        Visit(root);
        return values;

        void Visit(YamlNode node)
        {
            switch (node)
            {
                case YamlScalarNode { Value: { } value }:
                    values.Add(value);
                    break;
                case YamlMappingNode mapping:
                    foreach (var (key, value) in mapping.Children)
                    {
                        Visit(key);
                        Visit(value);
                    }

                    break;
                case YamlSequenceNode sequence:
                    foreach (var item in sequence.Children) Visit(item);
                    break;
            }
        }
    }

    private static bool DeclaresAnyContentsPermission(string content) =>
        ContentsValues(content).Count > 0;

    private static IReadOnlyList<string> ContentsValues(string content)
    {
        var values = new List<string>();
        foreach (var node in Documents(content))
        {
            Walk(node, values);
        }

        return values;

        static void Walk(YamlNode node, List<string> values)
        {
            switch (node)
            {
                case YamlMappingNode mapping:
                    foreach (var (key, value) in mapping.Children)
                    {
                        if (key is YamlScalarNode { Value: "permissions" }
                            && value is YamlMappingNode permissions)
                        {
                            foreach (var (name, granted) in permissions.Children)
                            {
                                if (name is YamlScalarNode { Value: "contents" }
                                    && granted is YamlScalarNode { Value: { } grant })
                                {
                                    values.Add(grant);
                                }
                            }
                        }

                        Walk(value, values);
                    }

                    break;
                case YamlSequenceNode sequence:
                    foreach (var item in sequence.Children) Walk(item, values);
                    break;
            }
        }
    }

    private static IReadOnlyList<string> TriggerNames(string content)
    {
        foreach (var document in Documents(content))
        {
            if (document is not YamlMappingNode root) continue;
            foreach (var (key, value) in root.Children)
            {
                // YAML 1.1 reads a bare `on` as the boolean true, so both spellings appear.
                if (key is not YamlScalarNode { Value: "on" or "True" or "true" }) continue;
                return value switch
                {
                    YamlMappingNode mapping => mapping.Children.Keys
                        .OfType<YamlScalarNode>()
                        .Select(static scalar => scalar.Value ?? string.Empty)
                        .OrderBy(static name => name, StringComparer.Ordinal)
                        .ToArray(),
                    YamlSequenceNode sequence => sequence.Children
                        .OfType<YamlScalarNode>()
                        .Select(static scalar => scalar.Value ?? string.Empty)
                        .OrderBy(static name => name, StringComparer.Ordinal)
                        .ToArray(),
                    YamlScalarNode scalar => [scalar.Value ?? string.Empty],
                    _ => [],
                };
            }
        }

        return [];
    }

    private static IEnumerable<YamlNode> Documents(string content)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(content));
        return stream.Documents.Select(static document => document.RootNode).ToArray();
    }

    private sealed record WorkflowSource(string Path, string Content);
}
