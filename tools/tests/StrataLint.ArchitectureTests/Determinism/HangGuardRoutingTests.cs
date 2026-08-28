namespace StrataLint.ArchitectureTests;

/// <summary>
/// hang-guard 预算的声明写着「never bears a test verdict」,但那只是**声明** ——
/// 只有当调用点走 <c>TestProcessRunner</c> 时,超时才会变成 `SkipException`;
/// 走 <c>BoundedProcessRunner</c> 时它抛 `TimeoutException`,于是**恰好承担了判词**。
/// 本类把「声明」与「路由」钉在一起(#3670)。
/// </summary>
public sealed class HangGuardRoutingTests
{
    /// <summary>
    /// 凡把 hang-guard 预算传给 <c>BoundedProcessRunner.Run</c> 的测试侧调用点,
    /// 都必须改走 <c>TestProcessRunner.Run</c>(它是同签名包装,只多一层 `Classify`)。
    ///
    /// **判据的两个例外,都是有理由的**:
    /// ① <c>TestProcessRunner.cs</c> 自身 —— 它就是那层包装;
    /// ② 传 <c>TestBudgets.ZeroDuration</c> 的调用点 —— 那是**故意**测超时行为
    ///    (`FaultInjectionTests`),它要的正是 `TimeoutException`。
    ///
    /// **已知盲区(写出来,因为一道不点名自己缺口的门比没有更糟)**:
    /// 本判据是**字面**匹配预算标识符。把预算先赋给局部变量、用类型别名、
    /// 或从别处返回一个 `TimeSpan` 再传进去,本测试都看不见。
    /// 这三种属「检查本身会不会被绕过」那一维,仍由评审守。
    /// </summary>
    [Fact]
    public void EveryHangGuardBudgetGoesThroughTheSkipClassifyingRunner()
    {
        var offenders = GitIndexRepositoryFiles
            .Enumerate(RepositoryLayout.FindRoot())
            .Where(static file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && !file.RelativePath.EndsWith("/TestProcessRunner.cs", StringComparison.Ordinal))
            .SelectMany(static file => UnroutedHangGuardCalls(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.True(
            offenders.Length == 0,
            "以下调用点把 hang-guard 预算传给了 BoundedProcessRunner.Run,超时会变成 TimeoutException "
            + "(测试失败)而不是 SkipException(基础设施跳过),与该预算「never bears a test verdict」"
            + "的声明相反:"
            + string.Join(", ", offenders)
            + "。改走 TestProcessRunner.Run 即可 —— 它是同签名包装。"
            + "若某处**故意**要 TimeoutException(测超时行为本身),请改用 TestBudgets.ZeroDuration。");
    }

    private static IEnumerable<string> UnroutedHangGuardCalls(string path, string source)
    {
        const string Call = "BoundedProcessRunner.Run(";
        for (var index = source.IndexOf(Call, StringComparison.Ordinal);
             index >= 0;
             index = source.IndexOf(Call, index + Call.Length, StringComparison.Ordinal))
        {
            // raw-string literal 里的示例代码不是真调用(RemoteStateIndependencePolicyTests 有三处)。
            if (CountOccurrences(source.AsSpan(0, index), "\"\"\"") % 2 == 1)
            {
                continue;
            }

            // 取**该调用自己的实参列表**(括号平衡),不用固定窗口 ——
            // 固定窗口会跨进相邻调用:第一版就因此把 `FaultInjectionTests.cs` 里
            // 那处**故意**用 `ZeroDuration` 的调用误报为违规(窗口跨到了 13 行之后
            // 另一处已正确路由的调用的预算上)。
            var arguments = ArgumentList(source, index + Call.Length);
            var carriesHangGuard = arguments.Contains("HangGuard", StringComparison.Ordinal)
                || arguments.Contains("HangDetectionBudget", StringComparison.Ordinal);
            if (carriesHangGuard)
            {
                yield return $"{path}:{CountOccurrences(source.AsSpan(0, index), "\n") + 1}";
            }
        }
    }

    private static string ArgumentList(string source, int start)
    {
        var depth = 0;
        for (var index = start; index < source.Length; index++)
        {
            var character = source[index];
            if (character == '(')
            {
                depth++;
            }
            else if (character == ')')
            {
                if (depth == 0)
                {
                    return source[start..index];
                }

                depth--;
            }
        }

        return source[start..];
    }

    private static int CountOccurrences(ReadOnlySpan<char> text, string needle)
    {
        var count = 0;
        var index = text.IndexOf(needle, StringComparison.Ordinal);
        while (index >= 0)
        {
            count++;
            text = text[(index + needle.Length)..];
            index = text.IndexOf(needle, StringComparison.Ordinal);
        }

        return count;
    }
}
