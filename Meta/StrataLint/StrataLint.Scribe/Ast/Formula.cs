using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Scribe;

public sealed record FormulaIdentifier
{
    private static readonly Regex Pattern = new(
        "^[A-Za-z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);

    private FormulaIdentifier(string value) => Value = value;

    public string Value { get; }

    public static FormulaIdentifier Create(string value) =>
        value is not null && Pattern.IsMatch(value)
            ? new FormulaIdentifier(value)
            : throw new ArgumentException("Formula identifier is not canonical.", nameof(value));

    public override string ToString() => Value;
}

public enum FormulaBinaryOperator
{
    Add,
    Subtract,
    Multiply,
}

public enum FormulaRelationOperator
{
    Equal,
    NotEqual,
}

public abstract record Formula
{
    private Formula() { }

    public sealed record Symbol(FormulaIdentifier Name) : Formula;

    public sealed record Number(long Value) : Formula;

    public sealed record Phi : Formula;

    public sealed record Psi : Formula;

    public sealed record Placeholder : Formula;

    public sealed record Integers : Formula;

    public sealed record Negate(Formula Operand) : Formula;

    public sealed record Absolute(Formula Operand) : Formula;

    public sealed record Binary(
        Formula Left,
        FormulaBinaryOperator Operator,
        Formula Right) : Formula;

    public sealed record Fraction(Formula Numerator, Formula Denominator) : Formula;

    public sealed record Subscript(Formula Base, Formula Index) : Formula;

    public sealed record Power(Formula Base, Formula Exponent) : Formula;

    public sealed record Floor(Formula Operand) : Formula;

    public sealed record Log(Formula Base, Formula Argument) : Formula;

    public sealed record Modulo(Formula Value, Formula Modulus) : Formula;

    public sealed record Sequence(Formula Element, Formula Index, Formula Domain) : Formula;

    public sealed record SetLiteral(ImmutableArray<Formula> Elements) : Formula;

    public sealed record SetBuilder(Formula Element, Formula Variable, Formula Domain) : Formula;

    public sealed record FunctionCall(
        FormulaIdentifier Name,
        ImmutableArray<Formula> Arguments) : Formula;

    public sealed record Relation(
        Formula Left,
        FormulaRelationOperator Operator,
        Formula Right) : Formula;
}
