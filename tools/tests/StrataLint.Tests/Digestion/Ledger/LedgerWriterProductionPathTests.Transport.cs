using System.Net;
using System.Net.Sockets;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LedgerWriterProductionPathTests
{
    [Theory]
    [InlineData("accept")]
    [InlineData("read")]
    public async Task DepositDelegatedCover_HangGuardRemainsInfrastructure(string stage)
    {
        using var listener = new TcpListener(IPAddress.Loopback, 0);
        listener.Start();
        using var cancellation = new CancellationTokenSource();
        using var peer = new TcpClient();
        var reading = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var completion = new TaskCompletionSource<ProcessOutput>(TaskCreationOptions.RunContinuationsAsynchronously);
        if (stage == "accept") cancellation.Cancel();
        var exchange = ExchangeDelegatedCover(listener, completion.Task, cancellation,
            _ => throw new InvalidOperationException("incomplete request reached cover"),
            () => reading.SetResult());
        if (stage == "read")
        {
            await peer.ConnectAsync((IPEndPoint)listener.LocalEndpoint);
            await reading.Task;
            cancellation.Cancel();
        }
        completion.SetResult(new ProcessOutput(17, [], []));

        var failure = await Assert.ThrowsAsync<SkipException>(async () => await exchange);

        Assert.StartsWith("infrastructure-hang-guard expired", failure.Message, StringComparison.Ordinal);
    }

    private static async Task<ProcessOutput> ExchangeDelegatedCover(
        TcpListener listener,
        Task<ProcessOutput> process,
        CancellationTokenSource cancellation,
        Func<IReadOnlyList<string>, (int Status, string Output)> cover,
        Action? reading = null)
    {
        Task<TcpClient>? connection = null;
        TcpClient? client = null;
        ProcessOutput output;
        try
        {
            connection = listener.AcceptTcpClientAsync(cancellation.Token).AsTask();
            client = await AwaitTransport(connection);
            var stream = client.GetStream();
            using var reader = new StreamReader(stream, leaveOpen: true);
            using var writer = new StreamWriter(stream, new UTF8Encoding(false), leaveOpen: true) { AutoFlush = true };
            var arguments = new List<string>();
            reading?.Invoke();
            while (await AwaitTransport(reader.ReadLineAsync(cancellation.Token).AsTask()) is { Length: > 0 } argument)
                arguments.Add(argument);
            var result = cover(arguments);
            await writer.WriteLineAsync(result.Status.ToString(System.Globalization.CultureInfo.InvariantCulture));
            await writer.WriteAsync(result.Output);
        }
        catch (OperationCanceledException) when (cancellation.IsCancellationRequested)
        {
            throw new SkipException("infrastructure-hang-guard expired during delegated cover transport");
        }
        finally
        {
            try
            {
                cancellation.Cancel();
                client?.Dispose();
                if (client is null) listener.Stop();
                if (connection is not null)
                {
                    try { using var unused = await connection; }
                    catch (OperationCanceledException) { }
                }
            }
            finally
            {
                output = await process;
            }
        }
        return output;

        async Task<T> AwaitTransport<T>(Task<T> transport)
        {
            var completed = await Task.WhenAny(transport, process);
            cancellation.Token.ThrowIfCancellationRequested();
            if (completed == process)
            {
                cancellation.Cancel();
                try { await transport; }
                catch (OperationCanceledException) { }
                var failed = await process;
                Assert.Fail("deposit exited without delegating cover-atom: "
                    + Encoding.UTF8.GetString(failed.StandardError));
            }
            return await transport;
        }
    }
}
