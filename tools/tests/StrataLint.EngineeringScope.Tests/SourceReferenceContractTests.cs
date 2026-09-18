using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class SourceReferenceContractTests
{
    [Fact]
    public void CanonicalVerificationEntryRejectsMissingSourceCommit()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var result = SharedBuildContractTests.Process(TestRepositoryLayout.FindRoot(), "make",
            ["truth-release-verify", "SOURCE_REF=refs/heads/integration-source", "OUT=" + fixture.Root]);
        Assert.Equal(2, result.Exit);
        Assert.Contains("verify-source requires an explicit source ref and commit", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void IntegrationSourceCannotEnterProductionAssembly()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var result = SharedBuildContractTests.Process(TestRepositoryLayout.FindRoot(), "python3", ["-B", "-c", """
            import pathlib, sys
            source, area = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(source/'tools/scripts/workflow'))
            import truth_release as owner
            def unexpected(*args): raise AssertionError('publication must reject before API or assembly')
            owner.api = owner.assemble = unexpected
            sys.argv = ['truth_release.py','prepare','--repository',str(source),'--output',str(area),
                        '--source-ref','refs/heads/integration-source','--source-commit','a'*40]
            raise SystemExit(owner.main())
            """, TestRepositoryLayout.FindRoot(), fixture.Root], new Dictionary<string, string> { ["GITHUB_REPOSITORY"] = "owner/repo" });
        Assert.Equal(2, result.Exit);
        Assert.Contains("publication requires refs/heads/dev", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("ahead", 0)]
    [InlineData("identical", 0)]
    [InlineData("unprotected", 2)]
    [InlineData("wrong-branch", 2)]
    [InlineData("invalid-ref", 2)]
    [InlineData("invalid-commit", 2)]
    [InlineData("invalid-tip", 2)]
    [InlineData("diverged", 2)]
    [InlineData("behind", 2)]
    [InlineData("wrong-merge-base", 2)]
    [InlineData("api-failure", 2)]
    [InlineData("malformed-branch", 2)]
    [InlineData("malformed-tip", 2)]
    [InlineData("malformed-comparison", 2)]
    [InlineData("malformed-merge-base", 2)]
    public void ExplicitProtectedSourceRequiresExactMembership(string scenario, int expected)
    {
        var result = SharedBuildContractTests.Process(TestRepositoryLayout.FindRoot(), "python3", ["-B", "-c", """
            import pathlib, sys
            source, scenario = pathlib.Path(sys.argv[1]), sys.argv[2]
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            from source_reference import validate_source_ref
            commit, tip, branch = 'a'*40, 'b'*40, 'integration-source/check'
            calls = []
            def api(path):
                calls.append(path)
                if scenario == 'api-failure': raise ValueError('API unavailable')
                if len(calls) == 1:
                    assert path == 'repos/owner/repo/branches/integration-source%2Fcheck', path
                    if scenario == 'malformed-branch': return []
                    if scenario == 'malformed-tip': return dict(name=branch, protected=True, commit=None)
                    return dict(name='dev' if scenario == 'wrong-branch' else branch,
                                protected=scenario != 'unprotected', commit=dict(sha='bad' if scenario == 'invalid-tip' else tip))
                assert path == f'repos/owner/repo/compare/{commit}...{tip}', path
                if scenario == 'malformed-comparison': return None
                if scenario == 'malformed-merge-base': return dict(status='ahead', merge_base_commit=[])
                return dict(status=scenario if scenario in ('diverged','behind','identical') else 'ahead',
                            merge_base_commit=dict(sha=tip if scenario == 'wrong-merge-base' else commit))
            try:
                selected = validate_source_ref('owner/repo', 'refs/heads/../dev' if scenario == 'invalid-ref' else 'refs/heads/'+branch,
                                               'HEAD' if scenario == 'invalid-commit' else commit, api)
                assert selected == branch
                assert len(calls) == 2
                print('SOURCE_VERIFIED '+selected)
            except (OSError, ValueError) as error:
                print('SOURCE_REJECTED '+str(error))
                raise SystemExit(2)
            """, TestRepositoryLayout.FindRoot(), scenario]);
        Assert.True(result.Exit == expected, result.Text);
        Assert.Contains(expected == 0 ? "SOURCE_VERIFIED" : "SOURCE_REJECTED", result.Text, StringComparison.Ordinal);
    }

}
