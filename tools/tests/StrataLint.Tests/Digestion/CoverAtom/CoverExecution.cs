using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed record CoverExecution(
    CommandResult Result,
    string After,
    string Before,
    BackfillInventoryDocument AfterDocument)
{
    internal void Deconstruct(
        out CommandResult result,
        out string after,
        out string before)
    {
        result = Result;
        after = After;
        before = Before;
    }
}
