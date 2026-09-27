using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed class BufferedConsole : ICliConsole
{
    private readonly StringBuilder output = new();
    private readonly StringBuilder error = new();

    internal string Output => output.ToString();

    internal string Error => error.ToString();

    public void WriteOutput(string value) => output.Append(value);

    public void WriteError(string value) => error.Append(value);
}
