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

    public sealed record Symbol : Formula
    {
        public Symbol(FormulaIdentifier name) =>
            Name = name ?? throw new ArgumentNullException(nameof(name));

        public FormulaIdentifier Name { get; }
    }

    public sealed record Number : Formula
    {
        public Number(long value) => Value = value >= 0
            ? value
            : throw new ArgumentOutOfRangeException(
                nameof(value),
                "Negative formula values use Formula.Negate.");

        public long Value { get; }
    }

    public sealed record Phi : Formula;

    public sealed record Psi : Formula;

    public sealed record Placeholder : Formula;

    public sealed record Integers : Formula;

    public sealed record Negate : Formula
    {
        public Negate(Formula operand) =>
            Operand = operand ?? throw new ArgumentNullException(nameof(operand));

        public Formula Operand { get; }
    }

    public sealed record Absolute : Formula
    {
        public Absolute(Formula operand) =>
            Operand = operand ?? throw new ArgumentNullException(nameof(operand));

        public Formula Operand { get; }
    }

    public sealed record Binary : Formula
    {
        public Binary(Formula left, FormulaBinaryOperator @operator, Formula right)
        {
            Left = left ?? throw new ArgumentNullException(nameof(left));
            Right = right ?? throw new ArgumentNullException(nameof(right));
            Operator = @operator is FormulaBinaryOperator.Add
                or FormulaBinaryOperator.Subtract
                or FormulaBinaryOperator.Multiply
                    ? @operator
                    : throw new ArgumentOutOfRangeException(nameof(@operator));
        }

        public Formula Left { get; }

        public FormulaBinaryOperator Operator { get; }

        public Formula Right { get; }
    }

    public sealed record Fraction : Formula
    {
        public Fraction(Formula numerator, Formula denominator)
        {
            Numerator = numerator ?? throw new ArgumentNullException(nameof(numerator));
            Denominator = denominator ?? throw new ArgumentNullException(nameof(denominator));
        }

        public Formula Numerator { get; }

        public Formula Denominator { get; }
    }

    public sealed record Subscript : Formula
    {
        public Subscript(Formula @base, Formula index)
        {
            Base = @base ?? throw new ArgumentNullException(nameof(@base));
            Index = index ?? throw new ArgumentNullException(nameof(index));
        }

        public Formula Base { get; }

        public Formula Index { get; }
    }

    public sealed record Power : Formula
    {
        public Power(Formula @base, Formula exponent)
        {
            Base = @base ?? throw new ArgumentNullException(nameof(@base));
            Exponent = exponent ?? throw new ArgumentNullException(nameof(exponent));
        }

        public Formula Base { get; }

        public Formula Exponent { get; }
    }

    public sealed record Floor : Formula
    {
        public Floor(Formula operand) =>
            Operand = operand ?? throw new ArgumentNullException(nameof(operand));

        public Formula Operand { get; }
    }

    public sealed record Log : Formula
    {
        public Log(Formula @base, Formula argument)
        {
            Base = @base ?? throw new ArgumentNullException(nameof(@base));
            Argument = argument ?? throw new ArgumentNullException(nameof(argument));
        }

        public Formula Base { get; }

        public Formula Argument { get; }
    }

    public sealed record Modulo : Formula
    {
        public Modulo(Formula value, Formula modulus)
        {
            Value = value ?? throw new ArgumentNullException(nameof(value));
            Modulus = modulus ?? throw new ArgumentNullException(nameof(modulus));
        }

        public Formula Value { get; }

        public Formula Modulus { get; }
    }

    public sealed record Sequence : Formula
    {
        public Sequence(Formula element, Formula index, Formula domain)
        {
            Element = element ?? throw new ArgumentNullException(nameof(element));
            Index = index ?? throw new ArgumentNullException(nameof(index));
            Domain = domain ?? throw new ArgumentNullException(nameof(domain));
        }

        public Formula Element { get; }

        public Formula Index { get; }

        public Formula Domain { get; }
    }

    public sealed record SetLiteral : Formula
    {
        public SetLiteral(ImmutableArray<Formula> elements) =>
            Elements = RequireValues(elements, nameof(elements));

        public ImmutableArray<Formula> Elements { get; }
    }

    public sealed record SetBuilder : Formula
    {
        public SetBuilder(Formula element, Formula variable, Formula domain)
        {
            Element = element ?? throw new ArgumentNullException(nameof(element));
            Variable = variable ?? throw new ArgumentNullException(nameof(variable));
            Domain = domain ?? throw new ArgumentNullException(nameof(domain));
        }

        public Formula Element { get; }

        public Formula Variable { get; }

        public Formula Domain { get; }
    }

    public sealed record FunctionCall : Formula
    {
        public FunctionCall(FormulaIdentifier name, ImmutableArray<Formula> arguments)
        {
            Name = name ?? throw new ArgumentNullException(nameof(name));
            Arguments = RequireValues(arguments, nameof(arguments));
        }

        public FormulaIdentifier Name { get; }

        public ImmutableArray<Formula> Arguments { get; }
    }

    public sealed record Relation : Formula
    {
        public Relation(Formula left, FormulaRelationOperator @operator, Formula right)
        {
            Left = left ?? throw new ArgumentNullException(nameof(left));
            Right = right ?? throw new ArgumentNullException(nameof(right));
            Operator = RequireRelationOperator(@operator, nameof(@operator));
        }

        public Formula Left { get; }

        public FormulaRelationOperator Operator { get; }

        public Formula Right { get; }
    }

    public sealed record RelationChain : Formula
    {
        public RelationChain(
            FormulaRelationOperator @operator,
            ImmutableArray<Formula> operands)
        {
            Operator = RequireRelationOperator(@operator, nameof(@operator));
            Operands = RequireValues(operands, nameof(operands), minimumCount: 2);
        }

        public FormulaRelationOperator Operator { get; }

        public ImmutableArray<Formula> Operands { get; }
    }

    private static ImmutableArray<Formula> RequireValues(
        ImmutableArray<Formula> values,
        string parameterName,
        int minimumCount = 0)
    {
        if (values.IsDefault
            || values.Length < minimumCount
            || values.Any(static value => value is null))
        {
            throw new ArgumentException(
                "Formula collection is default, too short, or contains null.",
                parameterName);
        }

        return values;
    }

    private static FormulaRelationOperator RequireRelationOperator(
        FormulaRelationOperator value,
        string parameterName) => value is FormulaRelationOperator.Equal
            or FormulaRelationOperator.NotEqual
                ? value
                : throw new ArgumentOutOfRangeException(parameterName);
}
