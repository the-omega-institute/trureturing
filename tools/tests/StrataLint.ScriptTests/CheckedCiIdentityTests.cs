using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CheckedCiIdentityTests
{
    [Theory]
    [InlineData("schedule")]
    [InlineData("repository_dispatch")]
    public void PublisherReportSourceRequiresMatchingCheckout(string eventName)
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", PublisherFixture,
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/checked-ci-identity.py"),
            temporary.Path, eventName], temporary.Path,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string PublisherFixture = """
        import json, os, subprocess, sys
        from pathlib import Path
        script, directory, event = sys.argv[1:]
        root = Path(directory)
        def git(*args):
            return subprocess.run(['git', '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                *args], cwd=root, check=True, capture_output=True, text=True).stdout.strip()
        git('init', '--quiet')
        (root/'input').write_text('selected source')
        git('add', '.'); git('commit', '--quiet', '-m', 'selected')
        head = git('rev-parse', 'HEAD')
        event_sha = git('commit-tree', git('rev-parse', 'HEAD^{tree}'), '-p', head, '-m', 'later event')
        git('checkout', '--detach', head)
        payload = root/'event.json'; payload.write_text('{}')
        env = {k:v for k,v in os.environ.items() if not k.startswith(('GITHUB_', 'STRATALINT_')) and k != 'BASE'}
        env.update(GITHUB_ACTIONS='true', GITHUB_EVENT_NAME=event, GITHUB_EVENT_PATH=str(payload),
            GITHUB_SHA=event_sha, GITHUB_WORKFLOW_SHA=event_sha,
            GITHUB_WORKFLOW_REF='owner/repo/.github/workflows/truth-release-publish.yml@refs/heads/dev',
            GITHUB_REPOSITORY='owner/repo', GITHUB_RUN_ID='35', GITHUB_RUN_ATTEMPT='1', GITHUB_JOB='produce')
        rows = []
        def case(label, args=(), updates=None, accepted=False):
            environment = dict(env, **(updates or {}))
            result = subprocess.run([sys.executable, script, '--repository', str(root),
                '--report-source-arguments', *args], cwd=root, env=environment, capture_output=True, text=True)
            rows.append(dict(label=label, arguments=list(args), environment=updates or {}, exit=result.returncode,
                stdout=result.stdout, stderr=result.stderr))
            assert result.returncode == (0 if accepted else 2), rows[-1]
            if accepted:
                assert result.stdout.splitlines() == ['--base', head], rows[-1]
                identity = json.loads(result.stderr.split('CI_CHECKED_IDENTITY ')[1])
                assert identity['event_sha'] == event_sha != head and identity['tested_head'] == head, identity
                assert identity['selected_source'] == head and identity['protected_base'] is None, identity
                assert identity['push_before'] is None and identity['push_after'] is None, identity
            else: assert 'CI_REPORT_SOURCE_INVALID' in result.stderr, rows[-1]
        case('explicit-selected', ['--base', head], accepted=True)
        case('environment-selected', updates={'STRATALINT_SOURCE_BASE':head}, accepted=True)
        case('duplicate-identical', ['--base', head, '--base', head], {'STRATALINT_SOURCE_BASE':head}, True)
        case('mismatched-checkout', ['--base', event_sha])
        for label, args, updates in (
            ('missing', [], {}), ('empty', ['--base', ''], {}),
            ('empty-environment', [], {'STRATALINT_SOURCE_BASE':''}),
            ('symbolic', ['--base', 'HEAD'], {}), ('zero', ['--base', '0'*40], {}),
            ('short', ['--base', head[:12]], {}), ('missing-object', ['--base', '1'*40], {}),
            ('duplicate-conflict', ['--base', head, '--base', event_sha], {}),
            ('environment-conflict', ['--base', head], {'STRATALINT_SOURCE_BASE':event_sha}),
            ('mixed-push', ['--base', head, '--push-before', '0'*40, '--push-head', head], {}),
            ('push-only', ['--push-before', '0'*40, '--push-head', head], {}),
            ('incomplete-push', ['--base', head, '--push-before', head], {}),
            ('missing-workflow', ['--base', head], {'GITHUB_WORKFLOW_SHA':''}),
            ('wrong-caller', ['--base', head], {'GITHUB_WORKFLOW_REF':'owner/repo/other.yml@refs/heads/dev'}),
            ('wrong-repository', ['--base', head], {'GITHUB_REPOSITORY':'another/repo'}),
            ('wrong-job', ['--base', head], {'GITHUB_JOB':'publish'}),
        ): case(label, args, updates)
        git('checkout', '-b', 'attached', head)
        case('attached-checkout', ['--base', head])
        print(json.dumps(dict(event=event, selected_source=head, event_sha=event_sha, cases=rows)))
        """;

    [Theory]
    [InlineData("pull_request_target", "default-workflow", true)]
    [InlineData("pull_request_target", "event-base-drift", true)]
    [InlineData("pull_request_target", "explicit-base", true)]
    [InlineData("pull_request_target", "conflicting-base", false)]
    [InlineData("pull_request_target", "wrong-parent", false)]
    [InlineData("push", "valid", true)]
    [InlineData("push", "initial", true)]
    [InlineData("push", "acquire-success", true)]
    [InlineData("push", "acquire-failure", false)]
    [InlineData("push", "explicit-push", true)]
    [InlineData("push", "conflicting-push", false)]
    [InlineData("push", "partial-push", false)]
    [InlineData("push", "planning-options", false)]
    [InlineData("push", "both-modes", false)]
    [InlineData("push", "deleted", false)]
    [InlineData("push", "wrong-after", false)]
    [InlineData("push", "missing-workflow", false)]
    [InlineData("local", "valid", false)]
    [InlineData("local", "explicit-base", true)]
    [InlineData("local", "explicit-push", true)]
    [InlineData("local", "environment-conflict", false)]
    [InlineData("local", "duplicate-conflict", false)]
    public void ReportArgumentsRequireConsistentExplicitOrActionsIdentity(string eventName, string change, bool accepted)
        => RunFixture(eventName, change, accepted, "report");

    [Theory]
    [InlineData("pull_request", "valid", true)]
    [InlineData("push", "valid", true)]
    [InlineData("pull_request_target", "default-workflow", true)]
    [InlineData("pull_request", "wrong-head", false)]
    [InlineData("pull_request", "wrong-parent", false)]
    [InlineData("pull_request", "default-workflow", false)]
    [InlineData("push", "default-workflow", true)]
    [InlineData("push", "initial", true)]
    [InlineData("push", "acquire-success", true)]
    [InlineData("push", "acquire-failure", false)]
    [InlineData("push", "missing-before", false)]
    [InlineData("push", "wrong-after", false)]
    [InlineData("push", "deleted", false)]
    [InlineData("push", "missing-object", false)]
    [InlineData("push", "malformed-before", false)]
    [InlineData("push", "missing-workflow", false)]
    [InlineData("schedule", "valid", false)]
    [InlineData("push", "foreign-source-options", false)]
    public void CheckedIdentityBindsRealGitParentsAndWorkflowRevision(string eventName, string change, bool accepted)
        => RunFixture(eventName, change, accepted, "identity");

    private static void RunFixture(string eventName, string change, bool accepted, string mode)
    {
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-c", Fixture,
            Path.Combine(root, "tools/scripts/workflow/checked-ci-identity.py"), temporary.Path,
            eventName, change, accepted ? "yes" : "no", mode], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string Fixture = """
        import json, os, subprocess, sys
        from pathlib import Path
        script, directory, event, change, accepted, mode = sys.argv[1:]
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
        payload.write_text(json.dumps({'before': base, 'after': merge, 'created': False, 'deleted': False, 'pull_request': {'number': 17,
            'head': {'sha': pr_head}, 'base': {'sha': base, 'ref': 'integration-ci-fixture-tests'}}}))
        environment = dict(os.environ, GITHUB_EVENT_NAME=event, GITHUB_EVENT_PATH=str(payload),
            GITHUB_SHA=merge, GITHUB_WORKFLOW_SHA=merge,
            GITHUB_WORKFLOW_REF='owner/repo/ci-fixture.yml@refs/pull/17/merge',
            GITHUB_REPOSITORY='owner/repo', GITHUB_RUN_ID='23', GITHUB_RUN_ATTEMPT='1',
            GITHUB_JOB='fixture-job', GITHUB_REF='refs/pull/17/merge')
        data=json.loads(payload.read_text())
        if change == 'event-base-drift': data['pull_request']['base']['sha'] = pr_head
        if change == 'initial': data.update(before='0'*40, created=True)
        if change == 'missing-before': data.pop('before')
        if change == 'wrong-after': data['after']=pr_head
        if change == 'deleted': data.update(after='0'*40, deleted=True)
        if change == 'missing-object': data['before']='1'*40
        if change == 'malformed-before': data['before']='HEAD^1'
        extra=[]
        if change.startswith('acquire-'):
            donor=root/'donor'; donor.mkdir()
            def donor_git(*args):
                return subprocess.run(['git', *args], cwd=donor, check=True, text=True, capture_output=True).stdout.strip()
            donor_git('init', '--quiet')
            donor_git('config', 'user.name', 'Pinned donor'); donor_git('config', 'user.email', 'pinned@example.invalid')
            (donor/'old.txt').write_text('nonancestor pinned endpoint')
            donor_git('add', '.'); donor_git('commit', '--quiet', '-m', 'pinned')
            data['before']=donor_git('rev-parse', 'HEAD') if change == 'acquire-success' else '1'*40
            git('remote', 'add', 'origin', str(donor))
            extra=['--acquire-pinned']
        payload.write_text(json.dumps(data))
        if change == 'wrong-head': environment['GITHUB_SHA'] = pr_head
        if change == 'wrong-parent':
            data=json.loads(payload.read_text()); data['pull_request']['head']['sha']=base
            payload.write_text(json.dumps(data))
        if change == 'default-workflow': environment['GITHUB_WORKFLOW_SHA'] = base
        if change == 'missing-workflow': environment.pop('GITHUB_WORKFLOW_SHA')
        environment.update(GITHUB_OUTPUT=str(root/'outputs'), GITHUB_ENV=str(root/'environment'))
        arguments = ['--github-output', '--github-env']
        if change == 'foreign-source-options': arguments += ['--base', base]
        if mode == 'report':
            environment.update(STRATALINT_SOURCE_BASE='', STRATALINT_PUSH_BEFORE='', STRATALINT_PUSH_HEAD='')
            environment['GITHUB_ACTIONS'] = 'true' if event != 'local' else ''
            arguments = ['--report-source-arguments']
            if change == 'explicit-base': arguments += ['--base', base]
            if change == 'explicit-push': arguments += ['--push-before', data['before'], '--push-head', merge]
            if change == 'conflicting-base': arguments += ['--base', pr_head]
            if change == 'conflicting-push': arguments += ['--push-before', pr_head, '--push-head', merge]
            if change == 'partial-push': arguments += ['--push-before', base]
            if change == 'planning-options': arguments += ['--planning-before', base, '--planning-head', merge]
            if change == 'both-modes': arguments += ['--base', base, '--push-before', base, '--push-head', merge]
            if change == 'environment-conflict':
                environment['STRATALINT_SOURCE_BASE'] = pr_head
                arguments += ['--base', base]
            if change == 'duplicate-conflict': arguments += ['--base', base, '--base', pr_head]
        result=subprocess.run(['python3', script, '--repository', str(root), *arguments, *extra],
            cwd=root, env=environment, text=True, capture_output=True)
        assert (result.returncode == 0) == (accepted == 'yes'), (result.returncode, result.stdout, result.stderr)
        if mode == 'report':
            if accepted == 'yes':
                expected = ['--push-before', data['before'], '--push-head', merge] if event == 'push' or change == 'explicit-push' else ['--base', base]
                assert result.stdout.splitlines() == expected, result.stdout
                if event != 'local': assert 'CI_CHECKED_IDENTITY ' in result.stderr, result.stderr
            else:
                assert result.returncode == 2 and 'CI_REPORT_SOURCE_INVALID' in result.stderr, result.stderr
            raise SystemExit(0)
        if accepted == 'yes':
            row=json.loads(result.stdout.removeprefix('CI_CHECKED_IDENTITY '))
            exported=dict(line.split('=', 1) for line in (root/'environment').read_text().splitlines())
            outputs=dict(line.split('=', 1) for line in (root/'outputs').read_text().splitlines())
            assert exported['STRATALINT_SOURCE_BASE'] == ('' if event == 'push' else base)
            assert exported['STRATALINT_SCRIBE_BASE'] == ('' if event == 'push' else base)
            assert exported['STRATALINT_PUSH_BEFORE'] == (data['before'] if event == 'push' else '')
            assert exported['STRATALINT_PUSH_HEAD'] == (merge if event == 'push' else '')
            assert outputs['protected_base'] == ('' if event == 'push' else base)
            assert outputs['planning_mode'] == ('initial' if change == 'initial' else 'endpoints')
            assert row['tested_head'] == merge
            assert row['protected_base'] == (None if event == 'push' else base)
            if event == 'push': assert row['push_before'] == data['before'] and row['push_after'] == merge
            assert row['pr_head'] == (None if event == 'push' else pr_head)
            assert row['workflow_sha'] == environment['GITHUB_WORKFLOW_SHA']
            assert row['candidate_workflow'] == (change != 'default-workflow')
            assert row['event'] == event and row['job'] == 'fixture-job'
        else:
            assert 'CI_CHECKED_IDENTITY_INVALID' in result.stderr, result.stderr
        """;
}
