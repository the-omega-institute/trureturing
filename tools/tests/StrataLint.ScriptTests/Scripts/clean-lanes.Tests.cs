namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/clean-lanes.sh")]
public sealed class CleanLanesScriptTests
{

    [Fact]
    public void CleanLanesAdapterForwardsTheScopeFlagToTheCli()
    {
        // 路径写成字面量并内联 FindRoot():ScribeTestMapDeriver 只静态解析
        // Path.Combine(XxxRepositoryLayout.FindRoot(), "字面量") 这一形式;
        // 先赋值给 root 或改用常量都会判 VariablePath → unknown → 撞 SL-003 棘轮。
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/clean-lanes.sh"));

        // 开关必须一路透到 CLI:断链的开关比没有开关更糟——它看起来限定了作用面,
        // 实际什么也没限定,而这里限定的是「会不会删掉正在跑的判官树」。
        // 钉住转发那一行本身,不是钉住「文本里出现过这个参数名」:后者在 case 分支里
        // 也命中,删掉转发行照样绿(实测变异 EXIT=0),那是格式校验冒充指向校验。
        Assert.Contains("arguments+=(--lanes-only)", script, StringComparison.Ordinal);
        Assert.Contains("--lanes-only", script, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", script, StringComparison.Ordinal);
        var parseIndex = script.IndexOf("--lanes-only", StringComparison.Ordinal);
        var execIndex = script.IndexOf("exec dotnet run", StringComparison.Ordinal);
        Assert.True(parseIndex >= 0, "clean-lanes adapter must accept the scope flag");
        Assert.True(execIndex > parseIndex, "flag parsing must precede the CLI invocation");
    }
}
