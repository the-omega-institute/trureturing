using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record CphiKernelSpec(
    int TermCount,
    int FractionalPartDecimalDigits,
    int FirstFibonacciIndex,
    int LastFibonacciIndex);

public enum ValueDefinitionStatus
{
    Emitted,
    RegisteredOpen,
}

public abstract record ValueComputation
{
    private ValueComputation()
    {
    }

    public sealed record ExactQuadratic(
        ExactRational RationalCoefficient,
        ExactRational SqrtFiveCoefficient) : ValueComputation;

    public sealed record Cphi(CphiKernelSpec Spec) : ValueComputation;
}

public sealed record ValueDefinition(
    string Id,
    string LeanGid,
    string LeanStatementSha256,
    ValueDefinitionStatus Status,
    string Definition,
    string? Formula,
    ImmutableDictionary<string, string> References,
    string? ExactValue,
    string? Error,
    string Method,
    string? ReferenceValue,
    string? ReferenceError,
    ValueComputation? Computation,
    string? OpenReason);
