using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Dunet;

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

[Union(EnableImplicitConversions = false)]
public partial record Formula
{
    public partial record Symbol(FormulaIdentifier Name);

    public partial record Number(long Value);

    public partial record Phi;

    public partial record Psi;

    public partial record Placeholder;

    public partial record Integers;

    public partial record Negate(Formula Operand);

    public partial record Absolute(Formula Operand);

    public partial record Binary(
        Formula Left,
        FormulaBinaryOperator Operator,
        Formula Right);

    public partial record Fraction(Formula Numerator, Formula Denominator);

    public partial record Subscript(Formula Base, Formula Index);

    public partial record Power(Formula Base, Formula Exponent);

    public partial record Floor(Formula Operand);

    public partial record Log(Formula Base, Formula Argument);

    public partial record Modulo(Formula Value, Formula Modulus);

    public partial record Sequence(Formula Element, Formula Index, Formula Domain);

    public partial record SetLiteral(ImmutableArray<Formula> Elements);

    public partial record SetBuilder(Formula Element, Formula Variable, Formula Domain);

    public partial record FunctionCall(
        FormulaIdentifier Name,
        ImmutableArray<Formula> Arguments);

    public partial record Relation(
        Formula Left,
        FormulaRelationOperator Operator,
        Formula Right);
}
