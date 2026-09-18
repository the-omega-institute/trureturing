namespace StrataLint.TestSupport;

internal static class HangGuardRouting
{
    internal static IReadOnlyList<string> FindUnroutedHangGuardCalls(string repositoryRoot)
    {
        var offenders = new List<string>();
        foreach (var file in StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot))
        {
            if (!file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                || !file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                || file.RelativePath.EndsWith("/TestProcessRunner.cs", StringComparison.Ordinal))
            {
                continue;
            }

            var source = File.ReadAllText(file.FullPath);
            offenders.AddRange(UnroutedHangGuardCalls(file.RelativePath, source));
        }

        return offenders.Order(StringComparer.Ordinal).ToArray();
    }

    private static IEnumerable<string> UnroutedHangGuardCalls(string path, string source)
    {
        const string Call = "BoundedProcessRunner.Run(";
        for (var index = source.IndexOf(Call, StringComparison.Ordinal);
             index >= 0;
             index = source.IndexOf(Call, index + Call.Length, StringComparison.Ordinal))
        {
            // raw-string literal 里的示例代码不是真调用。
            if (CountText(source[..index], "\"\"\"") % 2 == 1)
            {
                continue;
            }

            // 取**该调用自己的实参列表**(括号平衡)。固定窗口会跨进相邻调用:
            // 第一版正因此把一处**故意**用 `ZeroDuration` 的调用误报为违规。
            var arguments = BalancedArguments(source, index + Call.Length);
            if (arguments.Contains("HangGuard", StringComparison.Ordinal)
                || arguments.Contains("HangDetectionBudget", StringComparison.Ordinal))
            {
                yield return $"{path}:{CountText(source[..index], "\n") + 1}";
            }
        }
    }

    private static string BalancedArguments(string source, int start)
    {
        var depth = 0;
        for (var index = start; index < source.Length; index++)
        {
            if (source[index] == '(')
            {
                depth++;
            }
            else if (source[index] == ')')
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

    private static int CountText(string text, string needle)
    {
        var count = 0;
        var index = text.IndexOf(needle, StringComparison.Ordinal);
        while (index >= 0)
        {
            count++;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal);
        }

        return count;
    }
}
