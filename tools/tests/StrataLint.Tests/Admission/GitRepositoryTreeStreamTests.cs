using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed class GitRepositoryTreeStreamTests
{
    private const string ObjectId = "1111111111111111111111111111111111111111";

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void RevisionReadersStreamInventoriesLargerThanTheBufferedOutputLimit(int mode)
    {
        using var repository = new TemporaryDirectory();
        var runner = new LargeTreeRunner();
        var gateway = new GitRepositoryGateway(repository.Path, runner, "git");
        var snapshot = mode switch
        {
            0 => gateway.ReadRevisionProjection("fixture", static _ => false),
            1 => gateway.ReadRevision("fixture"),
            _ => gateway.ReadRevision("fixture", ["selected.txt"]),
        };
        Assert.True(runner.TreeBytes > GitRepositoryGateway.DefaultGitOutputBytes);
        Assert.Equal(mode == 2 ? 1 : LargeTreeRunner.PathCount + 1, snapshot.Entries.Length);
        if (mode != 2) Assert.Equal(snapshot.Entries.Length, snapshot.PathInventory.Length);
        else Assert.True(snapshot.PathInventory.IsDefault);
        Assert.Contains(snapshot.Entries, entry => entry.Path == "selected.txt");
        if (mode != 2)
            Assert.Contains(snapshot.Entries, entry => entry.Path.EndsWith("/16999.txt", StringComparison.Ordinal));
        Assert.All(snapshot.Entries, entry => Assert.Empty(entry.Bytes));
    }

    [Fact]
    public async Task ParserPreservesByteFramingAcrossSingleByteReads()
    {
        var path = "nested/𐀀字\tname\n.txt";
        using var stream = new RecordStream([Encoding.UTF8.GetBytes($"100755 blob {ObjectId} 42\t{path}\0")], 1);
        var entry = Assert.Single(await GitRepositoryTreeStream.Parse(stream, CancellationToken.None));
        Assert.Equal(path, entry.Path);
        Assert.Equal("100755", entry.Mode);
        Assert.Equal(ObjectId, entry.ObjectId);
        Assert.Equal(42, entry.Size);
    }

    [Theory]
    [InlineData("invalid\0")]
    [InlineData("100644 blob oid 0\t../escape\0")]
    [InlineData("100644 blob oid -1\tfile\0")]
    [InlineData("100644 blob oid 0\tfile")]
    [InlineData("\0")]
    public async Task ParserRejectsMalformedAndIncompleteRecords(string output)
    {
        using var stream = new RecordStream([Encoding.UTF8.GetBytes(output)], 3);
        await Assert.ThrowsAsync<InvalidOperationException>(() => GitRepositoryTreeStream.Parse(stream, CancellationToken.None));
    }

    [Fact]
    public async Task ParserRejectsInvalidUtf8()
    {
        using var stream = new RecordStream([Encoding.UTF8.GetBytes($"100644 blob {ObjectId} 0\t").Concat(new byte[] { 255, 0 }).ToArray()], 1);
        await Assert.ThrowsAsync<DecoderFallbackException>(() => GitRepositoryTreeStream.Parse(stream, CancellationToken.None));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StreamedTreeFailureRetainsGitInfrastructureClassification(bool scoped)
    {
        using var repository = new TemporaryDirectory();
        var gateway = new GitRepositoryGateway(repository.Path, new LargeTreeRunner(fail: true), "git");
        var exception = Assert.Throws<GitInfrastructureException>(() => scoped
            ? gateway.ReadRevision("fixture", ["selected.txt"])
            : gateway.ReadRevision("fixture"));
        Assert.Contains("ls-tree", exception.Message, StringComparison.Ordinal);
        Assert.Contains("tree unavailable", exception.Message, StringComparison.Ordinal);
    }

    private sealed class LargeTreeRunner(bool fail = false) : IGitProcessRunner
    {
        internal const int PathCount = 17000;
        internal long TreeBytes { get; private set; }

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory,
            TimeSpan timeout, int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default)
        {
            Assert.Equal(new[] { "cat-file", "--batch" }, arguments);
            return new(0, Encoding.UTF8.GetBytes($"{ObjectId} blob 0\n\n"), []);
        }

        public StreamedProcessOutput<T> RunStreaming<T>(string fileName, IReadOnlyList<string> arguments,
            string workingDirectory, TimeSpan timeout, int maximumErrorBytes,
            Func<Stream, CancellationToken, Task<T>> readStandardOutput, ReadOnlyMemory<byte> standardInput = default)
        {
            Assert.Equal(GitRepositoryGateway.DefaultGitOutputBytes, maximumErrorBytes);
            if (arguments[0] != "ls-tree")
            {
                var result = Run(fileName, arguments, workingDirectory, timeout, standardInput: standardInput);
                using var body = new MemoryStream(result.StandardOutput);
                return new(0, readStandardOutput(body, CancellationToken.None).GetAwaiter().GetResult(), []);
            }
            Assert.Equal(new[] { "ls-tree", "-r", "-l", "-z", "fixture" }, arguments);
            using var stream = new RecordStream(fail ? [] : Records());
            var parsed = readStandardOutput(stream, CancellationToken.None).GetAwaiter().GetResult();
            TreeBytes = stream.BytesRead;
            return new(fail ? 128 : 0, parsed, fail ? Encoding.UTF8.GetBytes("tree unavailable") : []);
        }

        private static IEnumerable<byte[]> Records()
        {
            var prefix = string.Join("/", Enumerable.Repeat(new string('p', 200), 21));
            for (var index = 0; index < PathCount; index++)
                yield return Encoding.UTF8.GetBytes($"100644 blob {ObjectId} 0\t{prefix}/{index:D5}.txt\0");
            yield return Encoding.UTF8.GetBytes($"100644 blob {ObjectId} 0\tselected.txt\0");
        }
    }

    private sealed class RecordStream(IEnumerable<byte[]> records, int chunkSize = int.MaxValue) : Stream
    {
        private readonly IEnumerator<byte[]> records = records.GetEnumerator();
        private byte[] current = [];
        private int offset;
        internal long BytesRead { get; private set; }
        public override bool CanRead => true;
        public override bool CanSeek => false;
        public override bool CanWrite => false;
        public override long Length => throw new NotSupportedException();
        public override long Position { get => throw new NotSupportedException(); set => throw new NotSupportedException(); }
        public override int Read(byte[] buffer, int offset, int count) => Read(buffer.AsSpan(offset, count));
        public override int Read(Span<byte> buffer)
        {
            if (buffer.IsEmpty) return 0;
            if (offset == current.Length)
            {
                if (!records.MoveNext()) return 0;
                current = records.Current;
                offset = 0;
            }
            var count = Math.Min(Math.Min(buffer.Length, chunkSize), current.Length - offset);
            current.AsSpan(offset, count).CopyTo(buffer);
            offset += count;
            BytesRead += count;
            return count;
        }
        public override ValueTask<int> ReadAsync(Memory<byte> buffer, CancellationToken cancellationToken = default)
        {
            cancellationToken.ThrowIfCancellationRequested();
            return ValueTask.FromResult(Read(buffer.Span));
        }
        protected override void Dispose(bool disposing) { if (disposing) records.Dispose(); base.Dispose(disposing); }
        public override void Flush() => throw new NotSupportedException();
        public override long Seek(long offset, SeekOrigin origin) => throw new NotSupportedException();
        public override void SetLength(long value) => throw new NotSupportedException();
        public override void Write(byte[] buffer, int offset, int count) => throw new NotSupportedException();
    }
}
