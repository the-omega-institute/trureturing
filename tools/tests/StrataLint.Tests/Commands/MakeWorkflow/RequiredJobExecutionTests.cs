using System.Text;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

// 守卫只能守它跑得到的东西——而 required job 自己被跳过时,跑在它里面的守卫也不跑。
// 2026-08-17 实测(第七轮 F3):给 candidate-engineering 加 job 级 `if: false`,
// 现役 38 个 workflow 契约测试全过(compile_errors=0, exit=0);而 GitHub 把
// skipped required job 报为 Success 且不阻止合并。同理给真实测试步骤加
// `continue-on-error: true`,测试失败不再传播到 job 结论,38/38 照样全绿。
//
// 自指困境不成立,因为 `pull_request_target` 保证 workflow 文本来自 base:
// 提出该改动的那个 PR,其自身 CI 跑的是**未加 if 的 base workflow**,三个 required
// check 正常执行。故只要有一条契约在那时开口,该 PR 就进不来。守卫在合入前有机会说话。
//
// 判据写成产生处的形状,不写成"某某 job 不许加 if":required job 由 name 与分支保护的
// contexts 对应,凡这类 job 一律不得有 job 级 `if:`,其执行判决相关的步骤一律不得有
// `continue-on-error`。这是规则不是清单:未来新增的 required job 同样被逮住。
//
// 边界(不冒领):这守不住已有 admin 权限直接推 workflow 到 dev 的路径——那是
// enforce_admins=false,另有案在录(CLAUDE.md 第〇节勘注、第 19 条)。
public sealed class RequiredJobExecutionTests
{
    // 与分支保护 contexts 逐字对应(实测 2026-08-17)。
    private static readonly string[] RequiredCheckNames =
    [
        "Candidate harness engineering checks",
        "Canonical Lean report production",
        "Content-addressed dev baseline admission",
    ];

    [Fact]
    public void RequiredJobsCarryNoJobLevelCondition()
    {
        var offenders = RequiredJobs()
            .Where(static job => job.Value.Children.ContainsKey(new YamlScalarNode("if")))
            .Select(static job => job.Key)
            .ToArray();

        Assert.Empty(offenders);
    }

    [Fact]
    public void SuppressedStepFailureAlwaysReachesADownstreamDecision()
    {
        // 抑制失败本身不是病——病是抑制之后**没人再看它**。合法的两形:
        //   uses: 型(第三方 action,失败语义由 action 自己定,如 actions/cache/save)
        //   run:  型但有 id 且该 id 的 outcome **真的影响执行**(判词回落到别处,如 report-reuse:
        //         缓存服务失败 → 下游四个重活步骤以 `outcome != 'success'` 走完整生产路径)
        //
        // 2026-08-17 第八轮:首版判据是 workflow.Contains("steps.<id>.outcome") —— **纯文本匹配**,
        // 四席各自构造了不同的惰性引用全都骗过它:一行 YAML 注释;`if: false` 的步骤里 echo 它;
        // `false && steps.x.outcome != 'success'`。文本在场 ≠ 判词生效。
        // 故判据改为:该引用必须出现在**某个步骤自己的 `if:` 表达式**里(注释与 run 正文不算),
        // 且那个步骤本身不得是恒假门控(`if: false` / 以 `false &&` 起头)。
        var offenders = RequiredJobs()
            .SelectMany(job => Steps(job.Value)
                .Where(static step => step.Children.ContainsKey(new YamlScalarNode("continue-on-error")))
                .Where(step => !step.Children.ContainsKey(new YamlScalarNode("uses")))
                .Where(step => Scalar(step, "id") is not { Length: > 0 } id
                    || !HasEffectiveOutcomeConsumer(job.Value, id))
                .Select(step => job.Key + " / " + Scalar(step, "name")))
            .ToArray();

        Assert.Empty(offenders);
    }

    [Fact]
    public void EveryRequiredCheckNameResolvesToExactlyOneJob()
    {
        // 放行侧:名单与 workflow 必须真的对得上,否则前两条守的是空集。
        Assert.Equal(RequiredCheckNames.Length, RequiredJobs().Count);
    }

    [Fact]
    public void OutcomeConsumerRejectsCommentOnlyReference()
    {
        var job = JobFromYaml(
            "job:\n"
            + "  steps:\n"
            + "    - id: x\n"
            + "      continue-on-error: true\n"
            + "      run: exit 1\n"
            + "    # steps.x.outcome != 'success'\n"
            + "    - run: true\n");

        Assert.False(HasEffectiveOutcomeConsumer(job, "x"));
    }

    [Fact]
    public void OutcomeConsumerRejectsReferenceEchoedByAFalseStep()
    {
        var job = JobFromYaml(
            "job:\n"
            + "  steps:\n"
            + "    - id: x\n"
            + "      continue-on-error: true\n"
            + "      run: exit 1\n"
            + "    - if: false\n"
            + "      run: echo steps.x.outcome\n");

        Assert.False(HasEffectiveOutcomeConsumer(job, "x"));
    }

    [Fact]
    public void OutcomeConsumerRejectsFalseAndReference()
    {
        AssertOutcomeConsumerRejected("false && steps.x.outcome != 'success'");
    }

    [Fact]
    public void OutcomeConsumerRejectsTrueOrReference()
    {
        AssertOutcomeConsumerRejected("true || steps.x.outcome != 'success'");
    }

    [Fact]
    public void OutcomeConsumerRejectsAlwaysOrReference()
    {
        AssertOutcomeConsumerRejected("always() || steps.x.outcome != 'success'");
    }

    [Fact]
    public void OutcomeConsumerRejectsSelfComparison()
    {
        AssertOutcomeConsumerRejected("steps.x.outcome != steps.x.outcome");
    }

    [Fact]
    public void OutcomeConsumerRejectsConstantFromJsonReference()
    {
        AssertOutcomeConsumerRejected("fromJSON('false') && steps.x.outcome != 'success'");
    }

    [Fact]
    public void OutcomeConsumerRejectsOutOfDomainLiteral()
    {
        AssertOutcomeConsumerRejected("steps.x.outcome != 'not-a-real-outcome'");
    }

    [Fact]
    public void OutcomeConsumerRejectsUnknownExpressionComponent()
    {
        AssertOutcomeConsumerRejected("github.ref == 'refs/heads/dev' && steps.x.outcome != 'success'");
    }

    [Theory]
    [InlineData("steps.x.outcome == 'success'")]
    [InlineData("steps.x.outcome == 'failure'")]
    [InlineData("steps.x.outcome == 'cancelled'")]
    [InlineData("steps.x.outcome == 'skipped'")]
    [InlineData("always() && steps.x.outcome != 'success'")]
    [InlineData("false || steps.x.outcome == 'failure'")]
    public void OutcomeConsumerAcceptsAConditionThatVariesOverTheOutcomeDomain(string condition)
    {
        var job = JobWithStepCondition(condition);

        Assert.True(HasEffectiveOutcomeConsumer(job, "x"));
    }

    private static void AssertOutcomeConsumerRejected(string condition)
    {
        var job = JobWithStepCondition(condition);

        Assert.False(HasEffectiveOutcomeConsumer(job, "x"));
    }

    private static YamlMappingNode JobWithStepCondition(string condition)
    {
        return JobFromYaml(
            "job:\n"
            + "  steps:\n"
            + "    - id: x\n"
            + "      continue-on-error: true\n"
            + "      run: exit 1\n"
            + "    - id: consumer\n"
            + "      if: " + condition + "\n"
            + "      run: true\n");
    }

    private static YamlMappingNode JobFromYaml(string yaml)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(yaml));
        var root = (YamlMappingNode)stream.Documents.Single().RootNode;
        return (YamlMappingNode)((YamlMappingNode)root.Children[new YamlScalarNode("job")])!;
    }

    private static IReadOnlyList<KeyValuePair<string, YamlMappingNode>> RequiredJobs()
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(AdmissionWorkflowText()));
        var root = (YamlMappingNode)stream.Documents.Single().RootNode;
        var jobs = (YamlMappingNode)root.Children[new YamlScalarNode("jobs")];
        return jobs.Children
            .Where(static item => item.Value is YamlMappingNode)
            .Select(static item => new KeyValuePair<string, YamlMappingNode>(
                ((YamlScalarNode)item.Key).Value!,
                (YamlMappingNode)item.Value))
            .Where(static item => RequiredCheckNames.Contains(Scalar(item.Value, "name"), StringComparer.Ordinal))
            .ToArray();
    }

    // 「真的影响执行」= 出现在某步骤自身的 if: 表达式里,且该表达式的取值**真的随它变**。
    //
    // 两轮被绕的记录(黑名单打不赢):
    //   第八轮 首版是 workflow.Contains("steps.<id>.outcome") —— 纯文本匹配。
    //          注释、`if:false` 步骤里的 echo、`false && …` 三种惰性引用全部通过。
    //   第九轮 收窄为「非恒假门控」后仍被绕:`true || …`、`always() || …` —— **恒真**同样让引用失效,
    //          因为条件永远成立,outcome 是什么都无所谓。三席各自命中。
    //
    // 故改用**白名单形状**(本仓先例:#2249 的 strip 契约只接受规范直线程序):
    //   `||` 是让引用失效的唯一途径——析取的另一支恒真即短路,引用不再影响结果;
    //   `false` 常量让整个表达式恒假,步骤永不执行。
    //   两者皆禁,则表达式只剩合取,而合取中每一支都能改变结果。
    //
    // 边界(不冒领):这挡的是**无意中写错**,不是蓄意绕过——蓄意者仍可写一个形式合法却
    // 什么都不做的消费者步骤。静态检查无法判定「失败被妥善处理」。守护标为**早反馈**。
    private static bool HasEffectiveOutcomeConsumer(YamlMappingNode job, string id) =>
        Steps(job).Any(step =>
            Scalar(step, "if") is { Length: > 0 } condition
            && condition.Contains("steps." + id + ".outcome", StringComparison.Ordinal)
            && IsEffectiveComparison(condition, id));

    // 判据经四轮才写到点上:
    //   八轮 文本包含        → 注释 / if:false 里 echo / `false &&` 全过
    //   九轮 黑名单禁恒假     → `true ||`、`always() ||` 恒真同样让引用失效
    //   十轮 黑名单禁 || 与常量 → `steps.x.outcome != steps.x.outcome` 自比较恒假,仍过
    // 十一轮 白名单字符串比较 → fromJSON('false') 恒假 / 域外字面量恒真仍过。
    // 四次都是在列举形态；有效性的正面定义只能是语义的：在 outcome 的完整值域
    // { success, failure, cancelled, skipped } 上，条件求值必须同时出现 true 与 false。
    // 求值器只接受封闭、可静态求值的子语言；任何未知上下文或函数均 fail-closed。
    private static bool IsEffectiveComparison(string condition, string id) =>
        OutcomeConditionEvaluator.TryEvaluate(condition, id, out var values)
        && values.Contains(true)
        && values.Contains(false);

    private sealed class OutcomeConditionEvaluator
    {
        private static readonly string[] OutcomeDomain =
        [
            "success",
            "failure",
            "cancelled",
            "skipped",
        ];

        private readonly string text;
        private readonly string outcomeReference;
        private int position;

        private OutcomeConditionEvaluator(string condition, string id)
        {
            var normalized = condition.Trim();
            if (normalized.StartsWith("${{", StringComparison.Ordinal)
                && normalized.EndsWith("}}", StringComparison.Ordinal))
            {
                normalized = normalized[3..^2].Trim();
            }

            text = normalized;
            outcomeReference = "steps." + id + ".outcome";
        }

        internal static bool TryEvaluate(string condition, string id, out bool[] values)
        {
            var parser = new OutcomeConditionEvaluator(condition, id);
            var parsed = parser.ParseOr();
            parser.SkipWhitespace();
            if (parsed is not { Booleans: not null } result
                || parser.position != parser.text.Length)
            {
                values = [];
                return false;
            }

            values = result.Booleans;
            return true;
        }

        private EvaluationValue? ParseOr()
        {
            var left = ParseAnd();
            while (TryConsume("||"))
            {
                var right = ParseAnd();
                left = CombineBooleans(left, right, static (a, b) => a || b);
            }

            return left;
        }

        private EvaluationValue? ParseAnd()
        {
            var left = ParseEquality();
            while (TryConsume("&&"))
            {
                var right = ParseEquality();
                left = CombineBooleans(left, right, static (a, b) => a && b);
            }

            return left;
        }

        private EvaluationValue? ParseEquality()
        {
            var left = ParseUnary();
            if (TryConsume("=="))
            {
                return Compare(left, ParseUnary(), equal: true);
            }

            if (TryConsume("!="))
            {
                return Compare(left, ParseUnary(), equal: false);
            }

            return left;
        }

        private EvaluationValue? ParseUnary()
        {
            if (!TryConsume("!"))
            {
                return ParsePrimary();
            }

            var value = ParseUnary();
            return value is { Booleans: not null } boolean
                ? EvaluationValue.FromBooleans(boolean.Booleans.Select(static item => !item).ToArray())
                : null;
        }

        private EvaluationValue? ParsePrimary()
        {
            if (TryConsume("("))
            {
                var nested = ParseOr();
                return TryConsume(")") ? nested : null;
            }

            if (Peek() == '\'')
            {
                return TryReadString(out var literal)
                    ? EvaluationValue.FromStrings(Repeat(literal))
                    : null;
            }

            var identifier = ReadIdentifier();
            if (identifier.Length == 0)
            {
                return null;
            }

            if (string.Equals(identifier, "true", StringComparison.Ordinal))
            {
                return EvaluationValue.FromBooleans(Repeat(true));
            }

            if (string.Equals(identifier, "false", StringComparison.Ordinal))
            {
                return EvaluationValue.FromBooleans(Repeat(false));
            }

            if (string.Equals(identifier, outcomeReference, StringComparison.Ordinal))
            {
                return EvaluationValue.FromStrings(OutcomeDomain.ToArray());
            }

            if (!TryConsume("("))
            {
                return null;
            }

            if (string.Equals(identifier, "always", StringComparison.Ordinal)
                && TryConsume(")"))
            {
                return EvaluationValue.FromBooleans(Repeat(true));
            }

            if (string.Equals(identifier, "fromJSON", StringComparison.Ordinal)
                && TryReadString(out var json)
                && TryConsume(")"))
            {
                return json switch
                {
                    "true" => EvaluationValue.FromBooleans(Repeat(true)),
                    "false" => EvaluationValue.FromBooleans(Repeat(false)),
                    _ => null,
                };
            }

            return null;
        }

        private static EvaluationValue? CombineBooleans(
            EvaluationValue? left,
            EvaluationValue? right,
            Func<bool, bool, bool> combine) =>
            left is { Booleans: not null } leftBoolean
            && right is { Booleans: not null } rightBoolean
                ? EvaluationValue.FromBooleans(leftBoolean.Booleans
                    .Zip(rightBoolean.Booleans, combine)
                    .ToArray())
                : null;

        private static EvaluationValue? Compare(
            EvaluationValue? left,
            EvaluationValue? right,
            bool equal)
        {
            if (left is { Strings: not null } leftString
                && right is { Strings: not null } rightString)
            {
                return EvaluationValue.FromBooleans(leftString.Strings
                    .Zip(rightString.Strings, (a, b) => equal == string.Equals(a, b, StringComparison.Ordinal))
                    .ToArray());
            }

            if (left is { Booleans: not null } leftBoolean
                && right is { Booleans: not null } rightBoolean)
            {
                return EvaluationValue.FromBooleans(leftBoolean.Booleans
                    .Zip(rightBoolean.Booleans, (a, b) => equal == (a == b))
                    .ToArray());
            }

            return null;
        }

        private string ReadIdentifier()
        {
            SkipWhitespace();
            var start = position;
            while (position < text.Length
                && (char.IsLetterOrDigit(text[position])
                    || text[position] is '_' or '-' or '.'))
            {
                position++;
            }

            return text[start..position];
        }

        private bool TryReadString(out string value)
        {
            SkipWhitespace();
            value = string.Empty;
            if (Peek() != '\'')
            {
                return false;
            }

            position++;
            var result = new StringBuilder();
            while (position < text.Length)
            {
                if (text[position] != '\'')
                {
                    result.Append(text[position++]);
                    continue;
                }

                position++;
                if (position < text.Length && text[position] == '\'')
                {
                    result.Append('\'');
                    position++;
                    continue;
                }

                value = result.ToString();
                return true;
            }

            return false;
        }

        private bool TryConsume(string token)
        {
            SkipWhitespace();
            if (!text.AsSpan(position).StartsWith(token, StringComparison.Ordinal))
            {
                return false;
            }

            position += token.Length;
            return true;
        }

        private char? Peek()
        {
            SkipWhitespace();
            return position < text.Length ? text[position] : null;
        }

        private void SkipWhitespace()
        {
            while (position < text.Length && char.IsWhiteSpace(text[position]))
            {
                position++;
            }
        }

        private static T[] Repeat<T>(T value) => Enumerable.Repeat(value, OutcomeDomain.Length).ToArray();

        private sealed record EvaluationValue(bool[]? Booleans, string[]? Strings)
        {
            internal static EvaluationValue FromBooleans(bool[] values) => new(values, null);

            internal static EvaluationValue FromStrings(string[] values) => new(null, values);
        }
    }

    private static string AdmissionWorkflowText() =>
        File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    private static IEnumerable<YamlMappingNode> Steps(YamlMappingNode job) =>
        job.Children.TryGetValue(new YamlScalarNode("steps"), out var steps)
        && steps is YamlSequenceNode sequence
            ? sequence.Children.OfType<YamlMappingNode>()
            : [];

    private static string Scalar(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
        && value is YamlScalarNode scalar
            ? scalar.Value ?? string.Empty
            : string.Empty;
}
