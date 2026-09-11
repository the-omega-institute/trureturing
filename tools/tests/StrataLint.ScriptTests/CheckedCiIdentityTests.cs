using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CheckedCiIdentityTests
{
    [Theory]
    [InlineData("pull_request", "valid", true)]
    [InlineData("push", "valid", true)]
    [InlineData("pull_request_target", "default-workflow", true)]
    [InlineData("pull_request", "wrong-head", false)]
    [InlineData("pull_request", "wrong-parent", false)]
    [InlineData("pull_request", "default-workflow", false)]
    [InlineData("push", "default-workflow", false)]
    [InlineData("push", "missing-workflow", false)]
    [InlineData("schedule", "valid", false)]
    public void CheckedIdentityBindsRealGitParentsAndWorkflowRevision(string eventName, string change, bool accepted)
    {
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-c", Fixture,
            Path.Combine(root, "tools/scripts/workflow/checked-ci-identity.py"), temporary.Path,
            eventName, change, accepted ? "yes" : "no"], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string Fixture = """
        import json, os, subprocess, sys
        from pathlib import Path
        script, directory, event, change, accepted = sys.argv[1:]
        root = Path(directory)
        def git(*args):
            return subprocess.run(['git', *args], cwd=root, check=True, text=True,
                capture_output=True).stdout.strip()
        git('init', '--quiet')
        git('config', 'user.name', 'Identity fixture')
        git('config', 'user.email', 'identity@example.invalid')
        (root/'input.txt').write_text('baseline')
        git('add', '.')
        git('commit', '--quiet', '-m', 'base')
        base = git('rev-parse', 'HEAD')
        (root/'input.txt').write_text('candidate')
        git('add', '.')
        git('commit', '--quiet', '-m', 'head')
        pr_head = git('rev-parse', 'HEAD')
        tree = git('rev-parse', 'HEAD^{tree}')
        merge = git('commit-tree', tree, '-p', base, '-p', pr_head, '-m', 'tested merge')
        git('checkout', '--detach', merge)
        payload = root/'event.json'
        payload.write_text(json.dumps({'pull_request': {'number': 17,
            'head': {'sha': pr_head}, 'base': {'sha': base, 'ref': 'integration-ci-fixture-tests'}}}))
        environment = dict(os.environ, GITHUB_EVENT_NAME=event, GITHUB_EVENT_PATH=str(payload),
            GITHUB_SHA=merge, GITHUB_WORKFLOW_SHA=merge,
            GITHUB_WORKFLOW_REF='owner/repo/ci-fixture.yml@refs/pull/17/merge',
            GITHUB_REPOSITORY='owner/repo', GITHUB_RUN_ID='23', GITHUB_RUN_ATTEMPT='1',
            GITHUB_JOB='fixture-job', GITHUB_REF='refs/pull/17/merge')
        if change == 'wrong-head': environment['GITHUB_SHA'] = pr_head
        if change == 'wrong-parent':
            data=json.loads(payload.read_text()); data['pull_request']['head']['sha']=base
            payload.write_text(json.dumps(data))
        if change == 'default-workflow': environment['GITHUB_WORKFLOW_SHA'] = base
        if change == 'missing-workflow': environment.pop('GITHUB_WORKFLOW_SHA')
        result=subprocess.run(['python3', script, '--repository', str(root)],
            cwd=root, env=environment, text=True, capture_output=True)
        assert (result.returncode == 0) == (accepted == 'yes'), (result.returncode, result.stdout, result.stderr)
        if accepted == 'yes':
            row=json.loads(result.stdout.removeprefix('CI_CHECKED_IDENTITY '))
            assert row['tested_head'] == merge
            assert row['protected_base'] == base
            assert row['pr_head'] == (None if event == 'push' else pr_head)
            assert row['workflow_sha'] == environment['GITHUB_WORKFLOW_SHA']
            assert row['candidate_workflow'] == (change != 'default-workflow')
            assert row['event'] == event and row['job'] == 'fixture-job'
        else:
            assert 'CI_CHECKED_IDENTITY_INVALID' in result.stderr, result.stderr
        """;
}
