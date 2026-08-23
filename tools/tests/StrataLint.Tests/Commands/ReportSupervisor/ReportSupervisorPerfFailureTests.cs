using System.Text;

namespace StrataLint.Tests;

public sealed class ReportSupervisorPerfFailureTests
{
    [Fact]
    public void PerformanceWriterReportsInvalidConfigurationAsStructuredFailure()
    {
        using var fixture = new ReportSupervisorFixture();
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var library = Path.Combine(root, "tools", "scripts", "lib", "perf-event-lib.sh");
        var spool = Path.Combine(temporary.Path, "events.jsonl");
        File.WriteAllText(spool, "{}\n", new UTF8Encoding(false));

        var result = fixture.RunExternalProcess(
            "env",
            [
                "STRATALINT_PERF_CONFIGURATION=invalid/configuration",
                "bash", "-c", "source \"$1\"; perf_flush_events \"$2\" \"$3\" test-probe",
                "bash", library, root, spool,
            ],
            temporary.Path,
            4096);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            "{\"event\":\"performance_event_commit\",\"status\":\"failed\","
                + "\"source\":\"test-probe\",\"reason\":\"invalid-configuration\","
                + "\"exit_code\":1}\n",
            Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }
}
