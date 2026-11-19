using System.Text;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed class GitIndexRepositoryFilesTests
{
    private const string ObjectId = "1111111111111111111111111111111111111111";

    [Fact]
    public void StreamsCompleteIndexBeyondTheBufferedOutputLimit()
    {
        const int pathCount = 17000;
        var prefix = string.Join("/", Enumerable.Repeat(new string('p', 200), 21));
        IEnumerable<byte[]> Records()
        {
            for (var index = 0; index < pathCount; index++)
                yield return Encoding.UTF8.GetBytes($"100644 {ObjectId} 0\t{prefix}/{index:D5}.txt\0");
            yield return Encoding.UTF8.GetBytes($"100755 {ObjectId} 0\tlast.txt\0");
        }

        using var stream = new RecordStream(Records());
        var entries = GitIndexRepositoryFiles.Read(["--", ":(glob)**/*.txt"],
            (arguments, maximumErrorBytes, input, parse) =>
            {
                Assert.Equal(new[] { "ls-files", "--stage", "-z", "--", ":(glob)**/*.txt" }, arguments);
                Assert.Equal(64 * 1024 * 1024, maximumErrorBytes);
                Assert.True(input.IsEmpty);
                return new StreamedProcessOutput<Dictionary<string, GitIndexEntry>>(0,
                    parse(stream, CancellationToken.None).GetAwaiter().GetResult(), []);
            });
        Assert.True(stream.BytesRead > 64 * 1024 * 1024);
        Assert.Equal(pathCount + 1, entries.Count);
        Assert.Equal(new GitIndexEntry("100755", ObjectId), entries["last.txt"]);
        Assert.Contains(prefix + "/16999.txt", entries.Keys);
    }

    [Fact]
    public async Task PreservesFramingAndUtf8AcrossSingleByteReads()
    {
        const string path = "nested/𐀀字\tname\n.txt";
        using var stream = new RecordStream([Encoding.UTF8.GetBytes($"120000 {ObjectId} 0\t{path}\0")], 1);
        var entry = Assert.Single(await GitIndexRepositoryFiles.Parse(stream, CancellationToken.None));
        Assert.Equal(path, entry.Key);
        Assert.Equal(new GitIndexEntry("120000", ObjectId), entry.Value);
    }

    [Theory]
    [InlineData("invalid\0")]
    [InlineData("100644 oid 1\tfile\0")]
    [InlineData("100644 oid 0\tfile\0", "100755 oid 0\tfile\0")]
    [InlineData("100644 oid 0\tfile")]
    [InlineData("\0")]
    public async Task RejectsMalformedUnmergedDuplicateAndIncompleteRecords(string first, string second = "")
    {
        using var stream = new RecordStream([Encoding.UTF8.GetBytes(first + second)], 3);
        await Assert.ThrowsAsync<InvalidOperationException>(() =>
            GitIndexRepositoryFiles.Parse(stream, CancellationToken.None));
    }

    [Fact]
    public async Task RejectsInvalidUtf8()
    {
        using var stream = new RecordStream(
            [Encoding.UTF8.GetBytes($"100644 {ObjectId} 0\t").Concat(new byte[] { 255, 0 }).ToArray()], 1);
        await Assert.ThrowsAsync<DecoderFallbackException>(() =>
            GitIndexRepositoryFiles.Parse(stream, CancellationToken.None));
    }

    [Fact]
    public void PreservesGitFailureDiagnostics()
    {
        var exception = Assert.Throws<InvalidOperationException>(() => GitIndexRepositoryFiles.Read([],
            (_, _, _, _) => new(128, new(StringComparer.Ordinal), Encoding.UTF8.GetBytes("index unavailable"))));
        Assert.Equal("index unavailable", exception.Message);
    }

    [Fact]
    public async Task HonorsCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        using var stream = new RecordStream([]);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() =>
            GitIndexRepositoryFiles.Parse(stream, cancellation.Token));
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
