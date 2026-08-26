using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

// 一个 step output 被下游 step 以 env: 消费,就要经 execve 传递,而 Linux 单个环境变量
// 受 MAX_ARG_STRLEN(32 页 = 131072 字节)封顶。超了不是截断,是 E2BIG:消费方进程根本
// 起不来,连 ##[group]Run 都不打印,`if: always()` 也救不回来——日志零字节,红得毫无线索。
//
// 判据不写成"不许超过 N 字节"——运行期长度不可静态判。写成产生处的形状:凡导出到
// $GITHUB_OUTPUT 的标量,不得由自增累加(X="$X…" 或 X+=)构成。自增累加是无界增长的
// 唯一签名;不自增,则该值由单点赋值给出,有界与否一眼可判。全量明细走日志(宽通道),
// step output 只走有界标量(窄通道)。这是规则不是清单:任何未来新增的累加器同样被逮住。
public sealed class WorkflowOutputBoundTests
{
    // Linux fs/exec.c: MAX_ARG_STRLEN = 32 * PAGE_SIZE。单个 env 值超此即 E2BIG。
    private const int MaxEnvironmentVariableBytes = 32 * 4096;

    private static readonly Regex OutputExport = new(
        """(?m)^\s*(?:echo|printf)\b[^\r\n]*?["'](?<key>[A-Za-z_][A-Za-z0-9_]*)=\$(?:\{(?<name>[A-Za-z_][A-Za-z0-9_]*)\}|(?<name>[A-Za-z_][A-Za-z0-9_]*))["'][^\r\n]*>>\s*["']?\$\{?GITHUB_OUTPUT\}?["']?\s*$""",
        RegexOptions.CultureInvariant);

    [Fact]
    public void SelfAppendingAccumulatorIsNeverExportedAsAStepOutput()
    {
        Assert.Empty(UnboundedExports(AdmissionWorkflowText()));
    }

    [Fact]
    public void TheEnvironmentVariableCeilingIsTheOneLinuxEnforces()
    {
        // 常数写在这里是为了让判据的理由留在树上:319756 > 131072 是 #1829 红的原因。
        Assert.Equal(131072, MaxEnvironmentVariableBytes);
        Assert.True(319756 > MaxEnvironmentVariableBytes);
    }

    [Fact]
    public void AccumulatorExportIsDetected()
    {
        const string workflow = """
            jobs:
              check:
                steps:
                  - name: Accumulate
                    run: |
                      detail=""
                      for path in "${paths[@]}"; do
                        detail="$detail$path; "
                      done
                      echo "paths=$detail" >> "$GITHUB_OUTPUT"
            """;

        var violation = Assert.Single(UnboundedExports(workflow));
        Assert.Contains("Accumulate", violation, StringComparison.Ordinal);
        Assert.Contains("detail", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void PlusEqualsAccumulatorExportIsDetected()
    {
        const string workflow = """
            jobs:
              check:
                steps:
                  - name: Append
                    run: |
                      detail=""
                      detail+="one; "
                      echo "paths=$detail" >> "$GITHUB_OUTPUT"
            """;

        var violation = Assert.Single(UnboundedExports(workflow));
        Assert.Contains("Append", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void SinglePointAssignmentExportIsAccepted()
    {
        const string workflow = """
            jobs:
              check:
                steps:
                  - name: Count
                    run: |
                      detail=""
                      for path in "${paths[@]}"; do
                        printf 'SCOPE_CHANGED %s\n' "$path"
                      done
                      count="${#paths[@]}"
                      echo "changed_count=$count" >> "$GITHUB_OUTPUT"
            """;

        Assert.Empty(UnboundedExports(workflow));
    }

    // 只有被导出的那个名字受约束。日志侧的累加器不跨 env 边界,不该被误伤。
    [Fact]
    public void AccumulatorThatIsNeverExportedIsAccepted()
    {
        const string workflow = """
            jobs:
              check:
                steps:
                  - name: Log only
                    run: |
                      detail=""
                      for path in "${paths[@]}"; do
                        detail="$detail$path; "
                      done
                      printf 'SCOPE_DETAIL %s\n' "$detail"
                      echo "changed_count=$count" >> "$GITHUB_OUTPUT"
            """;

        Assert.Empty(UnboundedExports(workflow));
    }

    private static IEnumerable<string> UnboundedExports(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        foreach (var job in jobs.Children.Values.OfType<YamlMappingNode>())
        {
            if (!job.Children.TryGetValue(new YamlScalarNode("steps"), out var steps))
            {
                continue;
            }

            foreach (var step in Assert.IsType<YamlSequenceNode>(steps).Children.OfType<YamlMappingNode>())
            {
                if (!step.Children.TryGetValue(new YamlScalarNode("run"), out var run)
                    || run is not YamlScalarNode { Value: { } script })
                {
                    continue;
                }

                var name = step.Children.TryGetValue(new YamlScalarNode("name"), out var label)
                    && label is YamlScalarNode { Value: { } text }
                        ? text
                        : "<unnamed step>";
                foreach (var export in OutputExport.Matches(script).Cast<Match>())
                {
                    var variable = export.Groups["name"].Value;
                    if (SelfAppends(script, variable))
                    {
                        yield return $"{name}: step output '{export.Groups["key"].Value}' exports "
                            + $"self-appending accumulator '{variable}', whose length is unbounded; "
                            + $"a consuming step receives it as an environment variable and Linux "
                            + $"caps one at {MaxEnvironmentVariableBytes} bytes";
                    }
                }
            }
        }
    }

    private static bool SelfAppends(string script, string variable)
    {
        var name = Regex.Escape(variable);
        return Regex.IsMatch(
            script,
            @"(?m)^\s*" + name + @"(?:\+=|=[""']?\$\{?" + name + @"\b)",
            RegexOptions.CultureInvariant);
    }

    private static string AdmissionWorkflowText() =>
        File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
}
