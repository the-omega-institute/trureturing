using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CiTransportTests
{
    [Theory]
    [InlineData(0)]
    [InlineData(7)]
    public void NativeCommandObservationPrecedesExitAndPreservesCapturedBytes(int status)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new CurrentExecutionContractTests.CandidateFixture();
        var result = SharedBuildContractTests.Process(temporary.Root, "python3", ["-B", "-c", """
            import json, os, pathlib, sys, tempfile
            repository, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(repository / 'tools/lean-inspector/tests'))
            from test_native_support import NativeTestSupport
            fixture = NativeTestSupport()
            fixture.temporary = tempfile.TemporaryDirectory(dir=root)
            fixture.root = pathlib.Path(fixture.temporary.name)
            fixture.env = dict(os.environ)
            seen = {'stdout': '', 'stderr': ''}
            def observe(stream, text):
                seen[stream] += text
                if seen['stdout'] == 'hello':
                    (fixture.root / 'prefix-ack').write_text('observed before exit')
                if seen == {'stdout': 'helloλ\n', 'stderr': 'error\n'}:
                    (fixture.root / 'complete-ack').write_text('observed before exit')
            child = r'''import os, pathlib, sys, time
            root = pathlib.Path(sys.argv[1])
            os.write(1, b'hello\xce')
            while not (root / 'prefix-ack').exists(): time.sleep(0.001)
            os.write(1, b'\xbb\n')
            os.write(2, b'error\n')
            while not (root / 'complete-ack').exists(): time.sleep(0.001)
            sys.exit(int(sys.argv[2]))
            '''
            try:
                result = fixture.guarded_command([sys.executable, '-c', child,
                    str(fixture.root), sys.argv[3]], observe_output=observe)
                print(json.dumps(dict(observed=seen, stdout=result.stdout,
                    stderr=result.stderr, exit=result.returncode)))
            finally:
                fixture.cleanup_fixture()
            """, TestRepositoryLayout.FindRoot(), temporary.Root, status.ToString()]);
        Assert.True(result.Exit == 0, result.Text);
        using var document = JsonDocument.Parse(result.Text);
        var row = document.RootElement;
        Assert.Equal(status, row.GetProperty("exit").GetInt32());
        Assert.Equal("helloλ\n", row.GetProperty("stdout").GetString());
        Assert.Equal("error\n", row.GetProperty("stderr").GetString());
        Assert.Equal("helloλ\n", row.GetProperty("observed").GetProperty("stdout").GetString());
        Assert.Equal("error\n", row.GetProperty("observed").GetProperty("stderr").GetString());
    }
}
