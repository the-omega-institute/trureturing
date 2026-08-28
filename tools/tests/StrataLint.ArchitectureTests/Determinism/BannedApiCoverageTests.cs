using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class BannedApiCoverageTests
{
    /// <summary>
    /// 每个 xUnit 判词项目都必须挂上确定性禁令(#3649)。
    ///
    /// **这一条守的是「项目集合完整性」,不是「禁令表内容」**(后者由
    /// <see cref="DeterminismBanNamesEveryWallClockAndDelaySymbol"/> 守)。
    /// 两者曾被写在同一批改动里,于是 PR #3612 撤销那条失败的内容扫描判据时,
    /// **把这一条也一并带走了** —— 禁令仍在,但「谁被禁令覆盖」自那以后无人 fail-closed 地判。
    ///
    /// 判据与其已知盲区都写在
    /// <c>ScribeTestMapDeriver.FindVerdictProjectsMissingDeterminismBan</c> 的注释里;
    /// 简言之:它读**项目文件**,故看得见 `NoWarn` 抑制,**看不见**源文件里的
    /// `#pragma warning disable RS0030`、`.editorconfig` 降级、以及被假 `Condition` 弄哑的接线。
    /// 那三种属「检查本身会不会被跳过」这一维,仍由评审守。
    /// </summary>
    [Fact]
    public void DeterminismBanIsAttachedToEveryVerdictProject()
    {
        var missing = ScribeTestMapDeriver.FindVerdictProjectsMissingDeterminismBan(
            RepositoryLayout.FindRoot());

        Assert.True(
            missing.Count == 0,
            "以下 xUnit 判词项目没有完整挂上确定性禁令(需同时具备 BannedApiAnalyzers 引用与 "
            + "BannedSymbols.Determinism.txt 的 AdditionalFiles,且不得以 NoWarn 抑制 RS0030):"
            + string.Join(", ", missing)
            + "。新增判词项目时请一并接线;若某项目**不应**受该禁令约束,"
            + "它需要先像 CompileFailProofProjectExemptions 那样建立自己的受治类,而不是静默地不挂。");
    }

    [Fact]
    public void CompileFailProofMarksEveryExpectedDiagnosticLine()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "tests", "BannedApiCompileFailProof",
            "BannedApiViolations.cs");

        Assert.Equal(27, File.ReadLines(path).Count(static line =>
            line.Contains("// banned-api-proof", StringComparison.Ordinal)));
    }

    [Fact]
    public void DeterminismBanNamesEveryWallClockAndDelaySymbol()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "Architecture", "BannedSymbols.Determinism.txt");
        var entries = File.ReadAllLines(path).ToHashSet(StringComparer.Ordinal);

        Assert.All(new[]
        {
            "M:System.Threading.Thread.Sleep(System.Int32);Use an injected synchronization primitive outside deterministic tests.",
            "M:System.Threading.Thread.Sleep(System.TimeSpan);Use an injected synchronization primitive outside deterministic tests.",
            "M:System.Threading.Tasks.Task.Delay(System.Int32);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.Int32,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
        }, entry => Assert.Contains(entry, entries));
        Assert.Contains(
            "T:System.Diagnostics.Stopwatch;Do not make test verdicts or diagnostics depend on machine speed.",
            entries);
    }

    [Fact]
    public void EngineeringCiComparesEveryMarkedLineWithAnRs0030Diagnostic()
    {
        var path = Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml");
        var workflow = File.ReadAllText(path);

        Assert.Contains("mapfile -t expected_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("grep -nF \"// banned-api-proof\"", workflow, StringComparison.Ordinal);
        Assert.Contains("mapfile -t actual_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("error RS0030", workflow, StringComparison.Ordinal);
        Assert.Contains(
            "test \"${#actual_lines[@]}\" -eq \"${#expected_lines[@]}\"",
            workflow,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightComparesEveryMarkedLineWithAnRs0030Diagnostic()
    {
        var preflight = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/preflight.sh"));

        Assert.Contains("expected_lines+=(\"$line\")", preflight, StringComparison.Ordinal);
        Assert.Contains("actual_lines+=(\"$line\")", preflight, StringComparison.Ordinal);
        Assert.Contains("error RS0030", preflight, StringComparison.Ordinal);
        Assert.Contains(
            "test \"${#actual_lines[@]}\" -eq \"${#expected_lines[@]}\"",
            preflight,
            StringComparison.Ordinal);
    }
}
