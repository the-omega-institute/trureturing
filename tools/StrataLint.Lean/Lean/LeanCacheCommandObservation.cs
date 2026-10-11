using System.Text.Json;

namespace StrataLint.EngineeringScope;

// Optional observations of the existing cache-reader route. No observation
// is a cache input, a verdict, or a replacement for the raw command outcome.
internal sealed class LeanCacheCommandObservation(string phasePath, string? stdoutPath, string? stderrPath)
{
    internal static LeanCacheCommandObservation? FromEnvironment() =>
        Environment.GetEnvironmentVariable("STRATALINT_INSPECTOR_PHASES") is { Length: > 0 } path
            ? new(path, CacheOutputPath("STRATALINT_INSPECTOR_CHILD_STDOUT"),
                CacheOutputPath("STRATALINT_INSPECTOR_CHILD_STDERR")) : null;

    private static string? CacheOutputPath(string variable) =>
        Environment.GetEnvironmentVariable(variable) is { Length: > 0 } path ? path + ".cache" : null;

    internal void Boundary(string phase, string boundary, string? command = null,
        IReadOnlyList<string>? arguments = null, string? cwd = null, int? rawExit = null, string? error = null)
    {
        try
        {
            var clock = TimeProvider.System;
            File.AppendAllText(phasePath, JsonSerializer.Serialize(new
            {
                phase, boundary, monotonic_ms = (long)(clock.GetTimestamp() * (1000.0 / clock.TimestampFrequency)),
                command, arguments, cwd, raw_exit = rawExit, error,
            }) + "\n");
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or ArgumentException
            or NotSupportedException)
        {
            Unavailable(exception);
        }
    }

    internal Stream? Output(Stream? original) => Tee(original, stdoutPath);
    internal Stream? Error(Stream? original) => Tee(original, stderrPath);
    private static Stream? Tee(Stream? original, string? path) =>
        string.IsNullOrEmpty(path) || original is ObservationStream ? original : new ObservationStream(original, path);

    private static void Unavailable(Exception error)
    {
        try { Console.Error.WriteLine("LEAN_CACHE_DIAGNOSTIC_UNAVAILABLE " + error.Message); }
        catch (Exception exception) when (exception is IOException or ObjectDisposedException) { }
    }

    private sealed class ObservationStream(Stream? original, string path) : Stream
    {
        private bool failed;
        public override bool CanRead => false;
        public override bool CanSeek => false;
        public override bool CanWrite => true;
        public override long Length => throw new NotSupportedException();
        public override long Position { get => throw new NotSupportedException(); set => throw new NotSupportedException(); }
        public override int Read(byte[] buffer, int offset, int count) => throw new NotSupportedException();
        public override long Seek(long offset, SeekOrigin origin) => throw new NotSupportedException();
        public override void SetLength(long value) => throw new NotSupportedException();
        public override void Flush() => original?.Flush();
        public override void Write(byte[] buffer, int offset, int count)
        {
            original?.Write(buffer, offset, count);
            if (failed) return;
            try
            {
                using var file = new FileStream(path, FileMode.Append, FileAccess.Write, FileShare.ReadWrite);
                file.Write(buffer, offset, count);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or ArgumentException
                or NotSupportedException)
            {
                failed = true;
                Unavailable(exception);
            }
        }
    }
}
