using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-030 —— 判官面不得物化非 HEAD 修订的文件(CLAUDE.md 第 19 条 base 判官永久禁止的机器投影)。
// 这些是对合成文本的规则判词测试,不断言本仓真实 workflow 的内容(器律⑦′ 的豁免类:
// 被测对象是消费 workflow/脚本文本的生产逻辑,删掉真实 workflow 后测试仍有意义)。
public sealed class JudgeSurfaceRevisionRuleTests
{
    private const string ScriptPath = "tools/scripts/workflow/gate-helper.sh";
    private const string HarnessGatePath = RuleFixture.HarnessGatePath;
    private const string WorkflowPath = RuleFixture.WorkflowPath;

    [Fact]
    public void WorktreeAddOnTheJudgeSurfaceIsRejected()
    {
        var findings = Evaluate(HarnessGatePath, "git -C candidate worktree add --detach \"$root\" \"$ENGINEERING_BASE\"\n");
        var finding = Assert.Single(findings);
        Assert.Equal(HarnessGatePath, finding.Path);
        Assert.Contains("worktree add", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("git -C candidate show \"HEAD^1:tools/scripts/workflow/floor.py\" > \"$RUNNER_TEMP/floor.py\"")]
    [InlineData("git -C candidate show \"HEAD^1:${CLASSIFIER_PATH}\" > \"$classifier\"")]
    [InlineData("workflow_address=\"$(git -C candidate show \"${workflow_ref}:.github/workflows/ci.yml\" | sha256sum)\"")]
    [InlineData("git show origin/dev:Meta/FILEMAP.toml > policy.toml")]
    [InlineData("git show 3a2a11e34b:tools/x.sh | bash")]
    [InlineData("git cat-file -p \"$BASE:$path\" > \"$path\"")]
    [InlineData("git cat-file -p \"$oid\" > out")]
    [InlineData("git cat-file -p HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file blob \"$oid\" > script.sh")]
    [InlineData("git cat-file tree \"$tree\"")]
    [InlineData("git cat-file --batch < requests")]
    [InlineData("git cat-file --batch-check < in")]
    [InlineData("git -C \"$ROOT\" archive --format=tar \"$base_sha\" | tar -xf - -C \"$BASE_TREE\"")]
    [InlineData("git archive HEAD^1 | tar -x")]
    [InlineData("git archive -o base.tar HEAD^1")]
    [InlineData("git worktree add --detach /tmp/h \"$ENGINEERING_BASE\"")]
    [InlineData("git worktree add /tmp/h origin/dev")]
    [InlineData("git checkout HEAD^1 -- tools/scripts/workflow/gate.sh")]
    [InlineData("git checkout \"$DEV_BASELINE_SHA\"")]
    [InlineData("git checkout -B lane/x origin/dev")]
    [InlineData("git restore --source=origin/dev tools/scripts/workflow/gate.sh")]
    [InlineData("git read-tree -u HEAD^1")]
    [InlineData("git read-tree -u \"$BASE\"")]
    [InlineData("git checkout-index -a --prefix=base/")]
    [InlineData("git worktree add --detach --lock --reason HEAD /tmp/h \"$BASE\"")]
    [InlineData("git worktree add --frobnicate /tmp/h")]
    [InlineData("git cat-file -p \"$BASE:tools/scripts/workflow/x.sh\" > out # -e only checks existence")]
    [InlineData("git cat-file blob \"$oid\" > -e")]
    [InlineData("git cat-file --textconv HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --frob HEAD")]
    [InlineData("git cat-file -p HEAD^{/derive}")]
    [InlineData("git --git-dir \"$dir\" cat-file -p \"$oid\"")]
    [InlineData("git -c core.quotepath=false show HEAD^1:tools/scripts/workflow/x.sh > x.sh")]
    [InlineData("git --work-tree \"$tree\" --git-dir \"$dir\" checkout \"$BASE\" -- tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add --detach /tmp/h 2>/tmp/h.log HEAD^1")]
    [InlineData("git show >out HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --prefix \"release HEAD\" HEAD^1 > base.tar")]
    [InlineData("git archive --add-file HEAD HEAD^1 >out.tar")]
    [InlineData("git restore -sHEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --source=HEAD --source=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git -C \"/tmp/review repo\" show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("git cat-file -e \"$(git show HEAD^1:tools/scripts/workflow/x.sh > out; printf HEAD)\"")]
    [InlineData("git 'show' HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("git --git-dir \"/tmp/base repo/.git\" show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git --frobnicate show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git checkout --frob HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("/usr/bin/git show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("x=`git show HEAD^1:tools/scripts/workflow/x.sh`")]
    [InlineData("git show HEAD^1:tools/scripts/workflow/x.sh#frag > out")]
    [InlineData("git worktree add /tmp/h $BASE # HEAD")]
    [InlineData("x=\"`git show HEAD^1:tools/scripts/workflow/x.sh >out`\"")]
    [InlineData("x=\"$(printf '%s' ')'; git show HEAD^1:tools/scripts/workflow/x.sh >out)\"")]
    [InlineData("{ git show HEAD^1:tools/scripts/workflow/x.sh >out; }")]
    [InlineData("( git show HEAD^1:tools/scripts/workflow/x.sh >out )")]
    [InlineData("git archive -- HEAD^1 > t.tar")]
    [InlineData("git archive -o/dev/null HEAD^1")]
    [InlineData("git checkout -blane/x origin/dev")]
    [InlineData("x=\"$(y=\"$(git show HEAD^1:tools/scripts/workflow/x.sh)\"; printf %s \"$y\")\"")]
    [InlineData("git worktree add -d '>' HEAD^1")]
    [InlineData("git restore -WsHEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file --path -e --filters HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("git show HEAD^1:tools/scripts/workflow/x.sh -- docs")]
    [InlineData("X=1 git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("! git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("cat <(git show HEAD^1:tools/scripts/workflow/x.sh >out)")]
    [InlineData("git worktree add -- -tmp HEAD^1")]
    [InlineData("printf '%s\\n' 'contents HEAD^1:tools/scripts/workflow/x.sh' | git cat-file --batch-command > out")]
    [InlineData("git cat-file --batch-command='%(objectname)' < in")]
    [InlineData("git worktree add -d '2'>out HEAD^1")]
    [InlineData("git worktree add -d \\2>out HEAD^1")]
    [InlineData("if git show HEAD^1:tools/scripts/workflow/x.sh >/dev/null; then :; fi")]
    [InlineData("while git show HEAD^1:tools/scripts/workflow/x.sh; do :; done")]
    [InlineData("git restore --sour=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add -d /tmp/review >|log HEAD^1")]
    [InlineData("git show >'>' HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show >\"$out\" HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show 2>'&1' HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show >out>x HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("{fd}>/tmp/out git show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("{fd}> /tmp/out git show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$'git' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$'\\x67it' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$'\\147it' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show $'HEAD^1\\x3atools/scripts/workflow/x.sh' > out")]
    [InlineData("git restore --recurse-submodules --source=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --no-recurse-submodules -s HEAD^1 tools/scripts/workflow/x.sh")]
    [InlineData("git checkout --recurse-submodules=on-demand HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("\\g\"i\"t show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file --textcon --path=CLAUDE.md \"$(git rev-parse HEAD^1:CLAUDE.md)\" >out")]
    [InlineData("git cat-file --textconv --path=p HEAD^1:p")]
    [InlineData("git show --pretty HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show --decorate-refs=x HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show -3 HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show :tools/scripts/workflow/x.sh")]
    [InlineData("git archive --remote=/tmp/other HEAD")]
    [InlineData("git checkout --track=direct HEAD^1 -- p")]
    [InlineData("git restore --sour HEAD^1 -- p")]
    [InlineData("git restore --no-recurse-submodules --source HEAD^1 p")]
    [InlineData("git worktree add --orphan -b br /tmp/w HEAD^1")]
    [InlineData("git worktree add --relative-paths /tmp/w HEAD^1")]
    [InlineData("git show --unified HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show -U HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show -X HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --list --no-list HEAD^1 > /tmp/base.tar")]
    [InlineData("git archive -l --no-list HEAD^1")]
    [InlineData("git read-tree --empty --no-empty HEAD^1")]
    [InlineData("$'\\547it' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git $'\\563how' HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git show \"$(printf %s HEAD^1:tools/scripts/workflow/x.sh)\"")]
    [InlineData("git show \"$obj\"")]
    [InlineData("git show $ref -- tools/scripts/workflow/x.sh")]
    [InlineData("$'git\\000tail' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$'git\\x00tail' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git $'show\\400x' HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git $'\\163how\\c@tail' HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$'\\147it\\c@' show HEAD^1:tools/scripts/workflow/x.sh")]
    // Bash's quote parser consumes the backslash pair after `\c` before finding the closing quote.
    [InlineData(": $'\\c\\\\'; git show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("x=$'\\c\\\\'; git show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --no-remote --remote=/tmp/other HEAD")]
    [InlineData("git $(printf show) HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git \"$(printf show)\" HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git `printf show` HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git $VERB HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("\"$(command -v git)\" show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$GIT -C candidate show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git restore --stag --source=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --sou=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("time -p git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("coproc fetch git show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("x=`echo \\`git show HEAD^1:tools/scripts/workflow/x.sh\\``")]
    public void MaterializingAnotherRevisionIsRejected(string line)
    {
        var finding = Assert.Single(Evaluate(ScriptPath, line + "\n"));
        Assert.Equal(ScriptPath, finding.Path);
    }

    [Theory]
    [InlineData("git show \"HEAD:$p\" > \"$p\"")]
    [InlineData("commit_epoch=\"$(git show -s --format=%ct HEAD)\"")]
    [InlineData("source_tree=\"$(git cat-file -p HEAD | sed -n 's/^tree //p')\"")]
    [InlineData("git cat-file -e \"$sha^{commit}\"")]
    [InlineData("git cat-file -e \"${BASE}:${MODULE_PATH}\"")]
    [InlineData("git cat-file -t \"$oid\"")]
    [InlineData("git cat-file -s \"$oid\"")]
    [InlineData("git cat-file blob HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file -p HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file -p HEAD^{tree}")]
    [InlineData("git archive --format=tar HEAD -- tools docs | tar -x")]
    [InlineData("git checkout -- tools/scripts/workflow/gate.sh")]
    [InlineData("git checkout -b lane/x")]
    [InlineData("git restore tools/scripts/workflow/gate.sh")]
    [InlineData("git restore --source=HEAD tools/scripts/workflow/gate.sh")]
    [InlineData("git restore -s HEAD tools/scripts/workflow/gate.sh")]
    [InlineData("git worktree add --detach /tmp/h HEAD")]
    [InlineData("git worktree add -b lane/x /tmp/h")]
    [InlineData("git worktree add /tmp/h")]
    [InlineData("git read-tree HEAD")]
    [InlineData("git read-tree -m HEAD^{tree}")]
    [InlineData("base_sha=\"$(git -C candidate rev-parse HEAD^1)\"")]
    [InlineData("workflow_address=\"$(git -C candidate rev-parse \"${workflow_ref}:.github/workflows/ci.yml\")\"")]
    [InlineData("git diff --name-only -z --no-renames HEAD^1 HEAD")]
    [InlineData("git worktree remove --force \"$root\"")]
    [InlineData("git worktree list --porcelain")]
    [InlineData("# git worktree add is forbidden here; see SL-030")]
    [InlineData("git worktree add --quiet --detach /tmp/h HEAD")]
    [InlineData("git worktree add --detach /tmp/h > log")]
    [InlineData("git worktree add --reason \"lane\" --lock /tmp/h")]
    [InlineData("git read-tree HEAD > log")]
    [InlineData("git cat-file -p HEAD:tools/scripts/workflow/x.sh > out # trailing")]
    [InlineData("git cat-file -p HEAD^{commit}")]
    [InlineData("git --no-pager show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git commit -q -m \"archive HEAD^1 notes\"")]
    [InlineData("obj=\"$(git cat-file -p HEAD)\"")]
    [InlineData("git -C \"/tmp/review repo\" show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add --detach /tmp/h 2>/tmp/h.log HEAD")]
    [InlineData("git restore -sHEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git archive --prefix \"release HEAD\" HEAD > base.tar")]
    [InlineData("echo \"$(git rev-parse HEAD^1)\"")]
    [InlineData("git cat-file -p HEAD>out")]
    [InlineData("git worktree add -d /tmp/h HEAD")]
    [InlineData("git read-tree --prefix x/ HEAD")]
    [InlineData("git show HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD:tools/scripts/workflow/x.sh 2>&1 | tee log")]
    [InlineData("git show HEAD:tools/scripts/workflow/x.sh # HEAD^1:tools/scripts/workflow/y.sh")]
    [InlineData("git worktree add /tmp/h # \"$BASE\"")]
    [InlineData("git archive -- HEAD >/dev/null")]
    [InlineData("git archive -o/dev/null HEAD")]
    [InlineData("git checkout -blane/x")]
    [InlineData("{ git show HEAD:tools/scripts/workflow/x.sh; }")]
    [InlineData("( git rev-parse HEAD^1 )")]
    [InlineData("printf '%s' '{ git show HEAD^1:x }'")]
    [InlineData("git worktree add -d '>' HEAD")]
    [InlineData("git restore -WsHEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD -- docs:notes")]
    [InlineData("git cat-file --path x -e HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add -- -tmp HEAD")]
    [InlineData("X=1 git rev-parse HEAD^1")]
    [InlineData("cat <(git show HEAD:tools/scripts/workflow/x.sh)")]
    [InlineData("git worktree add -d '2'>out HEAD")]
    [InlineData("git worktree add -d 2>out HEAD")]
    [InlineData("if git rev-parse HEAD^1; then :; fi")]
    [InlineData("git worktree add -d /tmp/review >|log HEAD")]
    [InlineData("git show >'>' HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD:tools/scripts/workflow/x.sh >'>' 2>'&1'")]
    [InlineData("{fd}>/tmp/out git show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("$'git' show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --recurse-submodules=on-demand HEAD")]
    [InlineData("git restore --no-recurse-submodules -s HEAD tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add --no-detach /tmp/h HEAD")]
    [InlineData("git restore --no-quiet --source HEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --no-verbose HEAD")]
    [InlineData("git restore --recurse-submodules --source=HEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --recurse-submodules=on-demand --source HEAD tools/scripts/workflow/x.sh")]
    [InlineData("git checkout --recurse-submodules=on-demand HEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("g\"\\i\"t show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --no-verbose HEAD >/dev/null")]
    [InlineData("git archive --no-worktree-attributes --no-prefix HEAD")]
    [InlineData("git archive -9 --format tar HEAD")]
    [InlineData("git show --decorate-refs 'HEAD^1:foo' HEAD")]
    [InlineData("git show -n 1 -S HEAD^1:x HEAD")]
    [InlineData("git show -L1,2:tools/scripts/workflow/x.sh HEAD")]
    [InlineData("git show --unknown-flag HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git checkout -d HEAD")]
    [InlineData("git checkout --track=direct -2 -3 --pathspec-file-nul HEAD")]
    [InlineData("git restore --sour=HEAD -- p")]
    [InlineData("git restore --no-source p")]
    [InlineData("git cat-file --no-mailmap -t HEAD^1")]
    [InlineData("git read-tree --index-output=/tmp/i --no-recurse-submodules -m HEAD HEAD^{tree}")]
    [InlineData("git worktree add --no-checkout -B br /tmp/w HEAD")]
    [InlineData("git worktree add --relative-paths /tmp/w HEAD")]
    [InlineData("git show --expand-tabs=4 HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git show --expand-tabs -U3 --stat=80 HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git show --grep x --since 2020 --diff-filter A HEAD")]
    [InlineData("git archive --no-list --list")]
    [InlineData("git read-tree --no-empty --empty")]
    [InlineData("$'\\547it' show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD -- \"$path\"")]
    [InlineData("git show \"HEAD:$path\" > \"$out\"")]
    [InlineData("$'git\\000tail' show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git $'\\163how\\c@tail' HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git $'\\cA' show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData(": $'\\c\\\\'; git show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --remote=/tmp/other --no-remote HEAD")]
    [InlineData("$GIT show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("\"$(command -v git)\" rev-parse HEAD^1")]
    [InlineData("\"$HOME/.elan/bin/lake\" --version")]
    [InlineData("\"$HOME/.elan/bin/elan\" toolchain install HEAD^1")]
    [InlineData("$X $Y HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("$GIT -C candidate show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("\"$gate\" --candidate x --base y")]
    [InlineData("[[ \"$rc\" -ne 0 && \"$rc\" -ne 3 ]]")]
    [InlineData("\"$tool\" --producer HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("\"$tool\" --producer show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git restore --source=HEAD^1 --source=HEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --source=HEAD^1 --no-source tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --no-recurse-submodules -u HEAD^{tree}")]
    [InlineData("git restore --staged --source=HEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --conflict=diff3 tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --sparse-checkout HEAD")]
    [InlineData("time -p git rev-parse HEAD^1")]
    public void ReadingHeadOrMetadataIsAllowed(string line)
    {
        Assert.Empty(Evaluate(ScriptPath, line + "\n"));
    }

    [Theory]
    // An operand-less `\c` leaves the quote intact (bash 3.2 keeps a literal backslash).
    [InlineData(": $'\\c'; git show HEAD^1:p")]
    [InlineData("x=$'\\c'; git show HEAD^1:p")]
    // A substitution is word content: a glued `#` is data; a separated `#` is a comment.
    [InlineData("x=\"$(printf %s $(printf x)#)\"; git show HEAD^1:p")]
    [InlineData("x=\"$(printf %s <(printf x)#)\"; git show HEAD^1:p")]
    [InlineData("x=\"$( $(printf x) # )\ngit show HEAD^1:p\n)\"")]
    [InlineData("x=\"$(printf $'\\')'; git show HEAD^1:p)\"")]
    [InlineData("x=\"$( (printf x); git show HEAD^1:p)\"")]
    // Bash >= 4 semantics: word-initial `#` immediately after `$(` is a comment;
    // bash 3.2 closes early. Keep the fail-closed contract for the CI shell.
    [InlineData("x=\"$(# )\ngit show HEAD^1:p\n)\"")]
    [InlineData("$'git\\c\u0905' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git $'show\\c\u0905' HEAD^1:tools/scripts/workflow/x.sh")]
    public void RepairedShellBoundariesRejectOtherRevision(string script)
    {
        Assert.Single(Evaluate(ScriptPath, script + "\n"));
    }

    [Theory]
    [InlineData(": $'\\c'; git show HEAD:p")]
    [InlineData("x=\"$(printf %s $(printf x)#)\"; git show HEAD:p")]
    [InlineData("x=\"$(printf %s <(printf x)#)\"; git show HEAD:p")]
    [InlineData("x=\"$( $(printf x) # )\ngit show HEAD:p\n)\"")]
    [InlineData("x=\"$(printf $'\\')'; git show HEAD:p)\"")]
    [InlineData("x=\"$(printf $'\\')')\"; git show HEAD:p")]
    [InlineData("x=\"$( (printf x); git show HEAD:p)\"")]
    [InlineData("x=\"$(# )\ngit show HEAD:p\n)\"")]
    // Bash masks the first UTF-8 byte: git + 03 a0 + tail is not the command git.
    [InlineData("$'\\147it\\c\u00e0tail' show HEAD^1:p")]
    // These git-shaped strings stay inside the enclosing double-quoted assignment.
    [InlineData("x=\"$(echo $(printf x)# ) git show HEAD^1:p\"")]
    [InlineData("x=\"$(echo <(printf x)# ) git show HEAD^1:p\"")]
    [InlineData("$'git\\c\u0905' show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git $'show\\c\u0905' HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("$'git\\c' show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("x=\"$(case x in x) git show HEAD^1:tools/scripts/workflow/x.sh;; esac)\"")] // declared-unsupported: a case-pattern ')' inside $(...) closes the substitution early (rule 19 fail-open counterexample)
    public void RepairedShellBoundariesAllowHeadAndNonCommands(string script)
    {
        Assert.Empty(Evaluate(ScriptPath, script + "\n"));
    }

    [Fact]
    public void EveryOffendingLineIsReportedWithItsLineNumber()
    {
        var text = "set -euo pipefail\ngit worktree add /tmp/base \"$BASE\"\necho ok\ngit show HEAD^1:tools/x.sh > x.sh\n";
        var findings = Evaluate(ScriptPath, text);
        Assert.Equal(2, findings.Length);
        Assert.Contains(findings, finding => finding.Message.Contains("line 2", StringComparison.Ordinal));
        Assert.Contains(findings, finding => finding.Message.Contains("line 4", StringComparison.Ordinal));
    }

    [Fact]
    public void GitInvocationInsideATrailingCommentIsNotACommand()
    {
        // The lexer sees quotes, so an unquoted word-initial `#` is a real shell comment; nothing
        // after it executes. (The earlier whitespace tokenizer reported this line fail-closed.)
        Assert.Empty(Evaluate(ScriptPath, "echo ok # git show HEAD^1:tools/scripts/workflow/x.sh\n"));
    }

    [Fact]
    public void CrLfTerminatedWorktreeAddIsRejected()
    {
        var finding = Assert.Single(Evaluate(ScriptPath, "git worktree add /tmp/h \"$BASE\"\r\n"));
        Assert.Contains("$BASE", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BackslashContinuationIsOneCommandReportedAtItsFirstLine()
    {
        var finding = Assert.Single(
            Evaluate(ScriptPath, "git \\\n  show HEAD^1:tools/scripts/workflow/x.sh > out\n"));
        Assert.Contains("line 1", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CompositeActionYamlIsOnTheJudgeSurfaceToo()
    {
        const string action = "runs:\n  steps:\n    - uses: actions/checkout@v4\n      with:\n        ref: ${{ github.event.pull_request.base.sha }}\n    - run: git show HEAD^1:tools/scripts/workflow/x.sh > out\n";
        var findings = Evaluate(".github/actions/probe/action.yml", action);
        Assert.Equal(2, findings.Length);
    }

    [Theory]
    [InlineData("      - run: git show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("        run: git worktree add /tmp/h \"$BASE\"")]
    [InlineData("      - run: \"git cat-file -p $oid\"")]
    [InlineData("        run: \"git show HEAD^1:tools/scripts/workflow/x.sh > out\" # explanation")]
    [InlineData("        run: 'git show HEAD^1:tools/scripts/workflow/x.sh' # note")]
    [InlineData("        \"run\": git show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("        run: \"\\x67it show HEAD^1:tools/scripts/workflow/x.sh > out\"")]
    [InlineData("      - run: \"git\\u0020show\\u0020HEAD^1:tools/scripts/workflow/x.sh >out\"")]
    [InlineData("        run: \"echo ready\\ngit show HEAD^1:tools/scripts/workflow/x.sh > out\"")]
    [InlineData("    steps: [{run: \"git show HEAD^1:tools/scripts/workflow/x.sh >out\"}]")]
    [InlineData("    steps: [{name: x, run: git show HEAD^1:tools/scripts/workflow/x.sh >out}]")]
    [InlineData("        run: !!str \"git show HEAD^1:tools/scripts/workflow/x.sh >out\"")]
    [InlineData("    steps: [{run: \"echo ready\"}, {run: \"git show HEAD^1:tools/scripts/workflow/x.sh\"}]")]
    [InlineData("    steps: [{run: \"echo '\"}, {run: \"git show HEAD^1:tools/scripts/workflow/x.sh\"}]")]
    [InlineData("    steps: [{name: a, run: echo ready}, {name: b, run: git show HEAD^1:tools/scripts/workflow/x.sh}]")]
    [InlineData("        \"run\" : \"git show HEAD^1:tools/scripts/workflow/x.sh >out\"")]
    [InlineData("        run : git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("    steps: [{\"run\" : \"git show HEAD^1:tools/scripts/workflow/x.sh\"}]")]
    [InlineData("        run: !!str\t\"git show HEAD^1:tools/scripts/workflow/x.sh\"")]
    [InlineData("        run: !custom\t'git show HEAD^1:tools/scripts/workflow/x.sh'")]
    [InlineData("        run: git $(printf show) HEAD^1:tools/scripts/workflow/x.sh")]
    public void WorkflowRunScalarsAreShell(string line)
    {
        var finding = Assert.Single(Evaluate(WorkflowPath, line + "\n"));
        Assert.Equal(WorkflowPath, finding.Path);
    }

    [Theory]
    [InlineData("      - run: |")]
    [InlineData("        run: git rev-parse HEAD^1")]
    [InlineData("      - name: show HEAD^1:tools/scripts/workflow/x.sh in a step name")]
    [InlineData("          git show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("      # ref: ${{ github.base_ref }} — a comment, not a checkout")]
    [InlineData("        run: \"git show HEAD:tools/scripts/workflow/x.sh\" # ok")]
    [InlineData("        run: \"git cat-file -p HEAD\\u000Agit rev-parse HEAD^1\"")]
    [InlineData("        run: !!str 'git rev-parse HEAD^1'")]
    [InlineData("    steps: [{run: \"echo ready\"}, {run: \"git show HEAD:tools/scripts/workflow/x.sh\"}]")]
    [InlineData("        run: !!str\t'git rev-parse HEAD^1'")]
    [InlineData("        run: !custom\t'git show HEAD:tools/scripts/workflow/x.sh'")]
    public void WorkflowLinesWithoutAMaterializationAreAllowed(string line)
    {
        Assert.Empty(Evaluate(WorkflowPath, line + "\n"));
    }

    [Fact]
    public void NestingDeeperThanTheLexerBoundIsFailClosed()
    {
        var nested = string.Concat(Enumerable.Repeat("$(", JudgeSurfaceShellLexer.MaximumDepth + 2))
            + "git rev-parse HEAD"
            + string.Concat(Enumerable.Repeat(")", JudgeSurfaceShellLexer.MaximumDepth + 2));
        var finding = Assert.Single(Evaluate(ScriptPath, "x=" + nested + "\n"));
        Assert.Contains("nesting deeper", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommentEndingInABackslashDoesNotSwallowTheNextLine()
    {
        var finding = Assert.Single(
            Evaluate(ScriptPath, "# note \\\n" + "git show HEAD^1:tools/scripts/workflow/x.sh > out\n"));
        Assert.Contains("line 2:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommentEndingInABackslashBeforeAHeadReadIsAllowed()
    {
        Assert.Empty(Evaluate(ScriptPath, "# note \\\n" + "git show HEAD:tools/scripts/workflow/x.sh\n"));
    }

    [Fact]
    public void CommentedParenthesisInsideDollarSubstitutionDoesNotCloseIt()
    {
        const string script = "x=\"$( # )\ngit show HEAD^1:tools/scripts/workflow/x.sh > out\n)\"\n";
        var finding = Assert.Single(Evaluate(ScriptPath, script));
        Assert.Contains("line 2:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommentedParenthesisInsideYamlDollarSubstitutionDoesNotCloseIt()
    {
        const string workflow = "steps:\n  - run: |\n      x=\"$( # )\n      git show HEAD^1:tools/scripts/workflow/x.sh > out\n      )\"\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("line 4:", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("x=\"$( # )\ngit show HEAD:tools/scripts/workflow/x.sh > out\n)\"")]
    [InlineData("x=\"$(printf '#')\"\ngit show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("x=\"$(echo a#b)\"; git show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("x=\"$( # )\necho ok\n)\"; git show HEAD:tools/scripts/workflow/x.sh")]
    public void DollarSubstitutionCommentCounterpartsAreAllowed(string script)
    {
        Assert.Empty(Evaluate(ScriptPath, script + "\n"));
    }

    [Fact]
    public void SecondCommandInAMultiLineScalarIsReportedAtItsOwnLine()
    {
        const string workflow = "      - run: |\n          echo ready\n          git show HEAD^1:tools/scripts/workflow/x.sh\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("line 3:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ContinuationSplitInsideAWordJoinsWithoutASeparator()
    {
        var finding = Assert.Single(
            Evaluate(ScriptPath, "git sh\\\n" + "ow HEAD^1:tools/scripts/workflow/x.sh > out\n"));
        Assert.Contains("line 1", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FoldedRunBlockIsOneShellCommand()
    {
        const string workflow = "      - run: >\n          git\n          show HEAD^1:tools/scripts/workflow/x.sh > out\n      - run: echo done\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        // The folded command starts on the block's first content line, after the `>` indicator.
        Assert.Contains("line 2:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckingOutTheBaseRefInAWorkflowIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: ${{ github.event.pull_request.base.sha }}\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Equal(WorkflowPath, finding.Path);
    }

    [Fact]
    public void InlineWorkflowBaseRefIsRejected()
    {
        const string workflow = "steps:\n  - with: { ref: '${{ github.base_ref }}' }\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Equal(WorkflowPath, finding.Path);
        Assert.Contains("a `ref:` naming the protected base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MultiLineDoubleQuotedRunScalarIsOneShellCommand()
    {
        const string workflow = "      - run: \"git show\n          HEAD^1:tools/scripts/workflow/x.sh\"\n      - run: echo done\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("line 1:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MultiLineSingleQuotedRunScalarIsOneShellCommand()
    {
        const string workflow = "      - run: !!str 'git show\n          HEAD^1:tools/scripts/workflow/x.sh'\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void EmptyLineInsideAQuotedRunScalarFoldsToANewline()
    {
        // YAML folds an empty line inside a quoted scalar to a line break, which is a shell command
        // separator: `git show` (HEAD) and a bare `HEAD^1:…` word are two commands, neither a read.
        const string workflow = "      - run: 'git show\n\n          HEAD^1:tools/scripts/workflow/x.sh'\n      - run: 'git show\n\n          HEAD^1:tools/scripts/workflow/x.sh > out'\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void MultiLineQuotedRunScalarReadingHeadIsAllowed()
    {
        const string workflow = "      - run: \"git show\n          HEAD:tools/scripts/workflow/x.sh\"\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Theory]
    [InlineData("      - run: \"git show HEAD^1:tools/scripts/workflow/x.sh\n")]
    [InlineData("        run: \"\\U00110000 git rev-parse HEAD\"\n")]
    [InlineData("steps: [{run: \"git rev-parse HEAD\"}\n")]
    [InlineData("run: &a [*a]\nrun: x\n")]
    public void YamlThatDoesNotParseIsFailClosed(string workflow)
    {
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("does not parse", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RunWithANonScalarValueIsFailClosed()
    {
        const string workflow = "steps:\n  - run: [git, show, 'HEAD^1:tools/scripts/workflow/x.sh']\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("not a scalar", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AnchoredRunScalarReachedThroughAnAliasIsJudgedOnce()
    {
        const string workflow = "x-steps: &steps\n  - run: git show HEAD^1:tools/scripts/workflow/x.sh\njobs:\n  a:\n    steps: *steps\n  b:\n    steps: *steps\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void MergeKeyMappingIsWalked()
    {
        const string workflow = "base: &base\n  run: git show HEAD^1:tools/scripts/workflow/x.sh\nstep:\n  <<: *base\n  name: x\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void MultiLinePlainRunScalarIsOneShellCommand()
    {
        const string workflow = "      - run: git show\n          HEAD^1:tools/scripts/workflow/x.sh\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void CommentInsideADecodedRunScalarEndsAtItsLine()
    {
        const string workflow = "      - run: \"echo ready # note\\ngit show HEAD^1:tools/scripts/workflow/x.sh\"\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void SecondDocumentIsScannedToo()
    {
        const string workflow = "run: echo one\n---\nrun: git show HEAD^1:tools/scripts/workflow/x.sh\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("line 3:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LiteralBlockWithIndentationAndChompingIndicatorIsPlainShell()
    {
        const string workflow = "      - run: |2-\n          git show HEAD^1:tools/scripts/workflow/x.sh\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void BackslashContinuationInsideABlockScalarIsOneCommand()
    {
        const string workflow = "      - run: |\n          git \\\n            show HEAD^1:tools/scripts/workflow/x.sh\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void BackslashContinuationInsideADoubleQuotedScalarIsOneCommand()
    {
        const string workflow = "      - run: \"git \\\\\\n  show HEAD^1:tools/scripts/workflow/x.sh\"\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void YamlNestingDeeperThanTheBoundIsFailClosed()
    {
        var workflow = "deep: " + new string('[', 70) + new string(']', 70) + "\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("nesting", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryFlowStepOnOneLineIsJudged()
    {
        const string workflow = "    steps: [{run: \"git show HEAD^1:tools/scripts/workflow/x.sh\"}, {run: \"git cat-file -p $oid\"}]\n";
        Assert.Equal(2, Evaluate(WorkflowPath, workflow).Length);
    }

    [Fact]
    public void EveryRefOnOneLineIsJudged()
    {
        const string workflow = "    steps: [{uses: actions/checkout@v4, with: {ref: main}}, {uses: actions/checkout@v4, with: {ref: '${{ github.base_ref }}'}}]\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("a `ref:` naming the protected base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void QuotedRefKeyWithSeparationSpaceIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      \"ref\" : \"${{ github.base_ref }}\"\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("a `ref:` naming the protected base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FoldedRunBlockWithSeparationSpaceIsOneShellCommand()
    {
        const string workflow = "      - \"run\" : >\n          git\n          show HEAD^1:tools/scripts/workflow/x.sh >out\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void TaggedBaseRefWithATabIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: !!str\t\"${{github.base_ref}}\"\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void TaggedFoldedRunBlockIsOneShellCommand()
    {
        const string workflow = "      - run: !!str >\n          git\n          show HEAD^1:tools/scripts/workflow/x.sh\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void TaggedLiteralRunBlockIsPlainShell()
    {
        const string workflow = "      - run: !!str |\n          git show HEAD^1:tools/scripts/workflow/x.sh\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void FoldedRunBlockKeepsTheBreakAroundAMoreIndentedLine()
    {
        const string workflow = "      - run: >\n          echo ready\n            git show HEAD^1:tools/scripts/workflow/x.sh\n          echo done\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("line 3:", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FoldedRunBlockWithAMoreIndentedHeadReadIsAllowed()
    {
        const string workflow = "      - run: >\n          echo ready\n            git show HEAD:tools/scripts/workflow/x.sh\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void EmptyLineInsideAFoldedRunBlockIsANewline()
    {
        // `git show` (HEAD) and a bare `HEAD^1:…` word are two commands, neither a read.
        const string workflow = "      - run: >\n          git show\n\n          HEAD^1:tools/scripts/workflow/x.sh\n      - run: echo done\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void FoldedRunBlockWithIndentationIndicatorIsOneShellCommand()
    {
        const string workflow = "      - run: >2\n          git\n          show HEAD^1:tools/scripts/workflow/x.sh >out\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void EscapedBaseRefInAWorkflowIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      \"ref\": \"${{ github.\\u0062ase_ref }}\"\n";
        Assert.Single(Evaluate(WorkflowPath, workflow));
    }

    [Fact]
    public void BracketSpelledBaseRefInAWorkflowIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: \"${{ github.event.pull_request['base']['sha'] }}\"\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Contains("a `ref:` naming the protected base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BracketSpelledHeadRefInAWorkflowIsAllowed()
    {
        const string bracketHead = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: \"${{ github.event.pull_request['head']['sha'] }}\"\n";
        const string literalHead = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: HEAD\n";
        Assert.Empty(Evaluate(WorkflowPath, bracketHead));
        Assert.Empty(Evaluate(WorkflowPath, literalHead));
    }

    [Fact]
    public void CheckingOutTheMergeRefInAWorkflowIsAllowed()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with: { ref: \"${{ github.event_name == 'pull_request_target' && format('refs/pull/{0}/merge', github.event.pull_request.number) || github.sha }}\", fetch-depth: 0 }\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Theory]
    [InlineData("tools/scripts/ingest.sh")]
    [InlineData("tools/scripts/agent/scope-freeze-delta.sh")]
    [InlineData("docs/develop/notes/base-judge.md")]
    public void PathsOutsideTheJudgeSurfaceAreNotEvaluated(string path)
    {
        Assert.Empty(Evaluate(path, "git worktree add /tmp/base \"$BASE\"\n"));
    }

    [Fact]
    public void UnchangedJudgeSurfaceFilesAreOutsideTheCandidateDelta()
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Baseline[ScriptPath] = "git worktree add /tmp/base \"$BASE\"\n";
        fixture.Files[ScriptPath] = fixture.Baseline[ScriptPath];
        fixture.Changes.Add(RuleFixture.BlueprintPath);

        Assert.Empty(Diagnostics(fixture.BuildScopeProbe(RawChangeSet.Create(fixture.Changes))));
    }

    [Fact]
    public void RuleIsRegisteredAsABlockingTrustRule()
    {
        var descriptor = Assert.Single(
            RuleCatalog.Default.Descriptors,
            item => item.Id == RuleId.CreateKnown(30));
        Assert.Equal(AdmissionEffect.Block, descriptor.AdmissionEffect);
        Assert.Equal("trust", descriptor.Category);
        Assert.Equal(RuleLifecycle.Active, descriptor.Lifecycle);
    }

    private static ImmutableArray<RuleFinding> Evaluate(string path, string text)
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Files[path] = text;
        fixture.Changes.Add(path);
        return Diagnostics(fixture.BuildScopeProbe(RawChangeSet.Create(fixture.Changes)));
    }

    private static ImmutableArray<RuleFinding> Diagnostics(RuleEvaluationContext context) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(30), context).Diagnostics
            .Select(static diagnostic => new RuleFinding(diagnostic.Path, diagnostic.Message))
            .ToImmutableArray();
}
