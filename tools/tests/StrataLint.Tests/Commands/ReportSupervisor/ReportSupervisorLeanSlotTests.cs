using System.Text;

namespace StrataLint.Tests;

// Lean 槽的容量命题独立成篇:它谈的是编排(几个 producer 能同时跑),与同目录那篇谈脚本
// 契约(退出码、指标、进程树回收)的测试不是同一件事。2026-08-15 因默认槽数由 1 改为 3
// 而重写时,原文件已 790 行、逼近 SL-003 的 800 硬线,顺势按第8条裂到既有子目录。
public sealed class ReportSupervisorLeanSlotTests
{
    // 2026-08-15 用户裁决:默认槽数 1 -> 5(同日先定 3,再定 5)。命题因此换了,不是删掉——
    // "槽机制会封顶"仍受钉,
    // 只是封顶值由默认值给出。两条一起看才完整:显式设 1 时仍然串行(机制还在),用默认值时
    // 两个 producer 允许重叠(默认值确实是 >1)。
    //
    // 留档的反对读数(用户已确认后仍要加槽):实测一次 Lean 构建自身即跑 10+ 个 lean 进程、
    // 每个约 85% CPU,全机 top 两次采样 idle 0.12%(28 核 / 96 GB)。故加槽不增吞吐,只把
    // 同样的核分成 N 份。内存不是约束(44 GB 空闲,单次构建总 RSS 11.5 GB)。
    [Fact]
    public void ExplicitSingleLeanSlotStillSerializesConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunExternalProcess(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker,
             fixture.PerformanceConfiguration, "1"],
            maximumOutputBytes: 1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"concurrent driver exited {result.ExitCode}; stdout: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + "; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.False(File.Exists(fixture.OverlapMarker));
        var metrics = fixture.ReadMetrics();
        Assert.Equal(2, metrics.Count);
        Assert.All(metrics, metric =>
        {
            Assert.Equal("lean-producer", metric.GetProperty("role").GetString());
            Assert.Equal(1, metric.GetProperty("concurrency_count").GetInt32());
        });
    }

    [Fact]
    public void DefaultLeanSlotCountAdmitsConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunExternalProcess(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker,
             fixture.PerformanceConfiguration],
            maximumOutputBytes: 1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"concurrent driver exited {result.ExitCode}; stdout: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + "; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.True(
            File.Exists(fixture.OverlapMarker),
            "the default slot count must admit two concurrent lean producers");
        var metrics = fixture.ReadMetrics();
        Assert.Equal(2, metrics.Count);
        Assert.Contains(
            metrics,
            metric => metric.GetProperty("concurrency_count").GetInt32() > 1);
    }
}
