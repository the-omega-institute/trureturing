using System.Collections.Immutable;

namespace StrataLint.Definitions;

public sealed record CphiKernelSpec(
    int TermCount,
    int FractionalPartDecimalDigits,
    int FirstFibonacciIndex,
    int LastFibonacciIndex)
{
    public static CphiKernelSpec Canonical { get; } = new(
        TermCount: 3_524_577,
        FractionalPartDecimalDigits: 40,
        FirstFibonacciIndex: 16,
        LastFibonacciIndex: 31);
}

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

public static class ValuesDefinitions
{
    public static ImmutableArray<ValueDefinition> All { get; } =
    [
        Exact("D5/Ah", "(5*sqrt(5)-3)/24", -3, 24, 5, 24),
        Open(
            "D5/Bh",
            "h-side epsilon coefficient",
            "The h-sequence, epsilon grid, and fit window are not defined executablely.",
            "-0.14076",
            "0.00007"),
        Exact("D5/C0", "phi/2", 1, 4, 1, 4),
        Cphi(),
        Exact("D5/E", "(137-61*sqrt(5))/24", 137, 24, -61, 24),
        Open(
            "D5/T0",
            "Sturmian-Dirichlet value at s=0",
            "The E(N) sequence and structured epsilon-Abel extrapolation parameters are not defined executablely.",
            "-0.0862145",
            "0.0000005"),
        Open(
            "D5/T1",
            "first moment of T",
            "The moment sequence and extraction window are not defined executablely.",
            "0.03182",
            "0.00002"),
        Open(
            "D5/c1",
            "2*sqrt(5)*T0 + (137-61*sqrt(5))/24",
            "The typed relation is known, but its T0 dependency remains untranslated.",
            "-0.3605727",
            "0.00015",
            formula: "2*sqrt(5)*T0+(137-61*sqrt(5))/24",
            references: new Dictionary<string, string>(StringComparer.Ordinal) { ["T0"] = "D5/T0" }),
        Open(
            "D5/c2",
            "(sqrt(5)-1)*Bh/2 + (3-7*sqrt(5)/2)*T0 + 3*sqrt(5)*T1 + (269*sqrt(5)-623)/48",
            "The typed relation is known, but T0, T1, and Bh remain untranslated.",
            "0.09465",
            "0.00015",
            formula: "(sqrt(5)-1)*Bh/2+(3-7*sqrt(5)/2)*T0+3*sqrt(5)*T1+(269*sqrt(5)-623)/48",
            references: new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Bh"] = "D5/Bh",
                ["T0"] = "D5/T0",
                ["T1"] = "D5/T1",
            }),
        Exact("D5/cstar", "sqrt(5)*phi", 5, 2, 1, 2),
        Open(
            "D5/delta.mean",
            "full-period mean of the exchange-loss profile",
            "The D(epsilon) kernel, 72-point epsilon grid, and second-order resonance correction are not specified executablely.",
            "-0.00000717",
            "0.00000003"),
        Exact("D5/hbar", "-0.5", -1, 2, 0, 1),
        Exact("D5/kappa", "1/(2*phi)", -1, 4, 1, 4),
        Exact("D5/s1", "(1+sqrt(5))/12", 1, 12, 1, 12),
    ];

    private static ValueDefinition Exact(
        string id,
        string exactValue,
        long rationalNumerator,
        long rationalDenominator,
        long radicalNumerator,
        long radicalDenominator) =>
        new(
            id,
            ValueDefinitionStatus.Emitted,
            exactValue,
            Formula: null,
            References: ImmutableDictionary<string, string>.Empty,
            ExactValue: exactValue,
            Error: "0",
            Method: "exact-quadratic",
            ReferenceValue: exactValue,
            ReferenceError: "0",
            new ValueComputation.ExactQuadratic(
                ExactRational.Create(rationalNumerator, rationalDenominator),
                ExactRational.Create(radicalNumerator, radicalDenominator)),
            OpenReason: null);

    private static ValueDefinition Cphi() =>
        new(
            "D5/Cphi",
            ValueDefinitionStatus.Emitted,
            "-(1/(2*pi))*sum(k>=1,cos(4*pi*k*phi)*cot(pi*k*phi)/k)",
            Formula: null,
            References: ImmutableDictionary<string, string>.Empty,
            ExactValue: null,
            Error: "0.000000011",
            Method: "int-exact+Neumaier+full-window",
            ReferenceValue: "0.045759332",
            ReferenceError: "0.000000011",
            new ValueComputation.Cphi(CphiKernelSpec.Canonical),
            OpenReason: null);

    private static ValueDefinition Open(
        string id,
        string definition,
        string reason,
        string referenceValue,
        string referenceError,
        string? formula = null,
        IReadOnlyDictionary<string, string>? references = null) =>
        new(
            id,
            ValueDefinitionStatus.RegisteredOpen,
            definition,
            formula,
            references is null
                ? ImmutableDictionary<string, string>.Empty
                : references.ToImmutableDictionary(StringComparer.Ordinal),
            ExactValue: null,
            Error: null,
            Method: "registered-open",
            ReferenceValue: referenceValue,
            ReferenceError: referenceError,
            Computation: null,
            OpenReason: reason);
}
