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
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    MemberOf,
    Divides,
    SubsetOf,
    Equivalent,
}

public enum FormulaLogicOperator
{
    And,
    Or,
    Implies,
    Iff,
}

public enum FormulaQuantifier
{
    ForAll,
    Exists,
}

public enum FormulaLayoutMode
{
    Inline,
    Display,
}

public enum FormulaLatexMacro
{
    Delta, Gamma, Lambda, Leftrightarrow, Re, Rightarrow, Sigma, Vert,
    Alpha, Begin, Beta, Cdot, Circ, DeltaLower, Ell, Emptyset, End, Equiv,
    Exists, Exp, Forall, Frac, GammaLower, Gcd, Ge, Geq, Iff, Implies, In,
    Infty, Int, Iota, Kappa, Ker, LambdaLower, Land, Langle, Le, Left, Leq,
    Lfloor, Lim, Log, Longrightarrow, Lor, Lvert, Mapsto, Mathbb, Mathbf,
    Mathcal, Mathrm, Max, Mid, Middle, Min, Mu, Neg, Neq, Nu, Omega,
    Operatorname, Overline, Perp, Phi, Pi, Pm, Prod, Psi, Qquad, Quad,
    Rangle, Rfloor, Rho, Right, Rvert, Setminus, SigmaLower, Sim, Sin, Sqrt,
    Subset, Subseteq, Sum, Tau, Text, Theta, Times, To, Varepsilon,
    Varnothing, Varphi, Widehat, Widetilde, Xi, Zeta,
    EscapedSpace, NegativeThinSpace, ThinSpace, SemicolonSpace, RowBreak,
    OpenBrace, CloseBrace,
}

public enum FormulaLatexSymbol
{
    Exclamation, Ampersand, Apostrophe, OpenParenthesis, CloseParenthesis,
    Asterisk, Plus, Comma, Minus, Period, Slash, Colon, Semicolon, LessThan,
    Equal, GreaterThan, OpenBracket, CloseBracket, Caret, Underscore, VerticalBar,
}

public abstract record Formula
{
    private Formula() { }

    public sealed record Aligned : Formula
    {
        public Aligned(ImmutableArray<Formula> rows) =>
            Rows = RequireValues(rows, nameof(rows), minimumCount: 1);

        public ImmutableArray<Formula> Rows { get; }
    }

    public sealed record LatexSequence : Formula
    {
        public LatexSequence(ImmutableArray<Formula> items) =>
            Items = FormulaLatexRules.RequireItems(
                RequireValues(items, nameof(items)),
                nameof(items));

        public ImmutableArray<Formula> Items { get; }
    }

    public sealed record LatexGroup : Formula
    {
        public LatexGroup(ImmutableArray<Formula> items) =>
            Items = FormulaLatexRules.RequireItems(
                RequireValues(items, nameof(items)),
                nameof(items));

        public ImmutableArray<Formula> Items { get; }
    }

    public sealed record LatexMacro(FormulaLatexMacro Value) : Formula;

    public sealed record LatexSymbol(FormulaLatexSymbol Value) : Formula;

    public sealed record LatexSpace : Formula;

    public sealed record LatexNewline : Formula;

    public sealed record LatexWord : Formula
    {
        public LatexWord(FormulaIdentifier value) =>
            Value = value ?? throw new ArgumentNullException(nameof(value));

        public FormulaIdentifier Value { get; }
    }

    public sealed record LatexDigits : Formula
    {
        public LatexDigits(ImmutableArray<byte> digits)
        {
            if (digits.IsDefaultOrEmpty || digits.Any(static digit => digit > 9))
            {
                throw new ArgumentException("LaTeX digits must be a nonempty decimal sequence.", nameof(digits));
            }

            Digits = digits;
        }

        public ImmutableArray<byte> Digits { get; }
    }

    public sealed record Layout : Formula
    {
        internal Layout(FormulaLayoutMode mode, Formula content)
        {
            Mode = mode;
            Content = content;
        }

        public FormulaLayoutMode Mode { get; }

        public Formula Content { get; }
    }

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

    public sealed record NamedConstant : Formula
    {
        public NamedConstant(FormulaIdentifier name) =>
            Name = name ?? throw new ArgumentNullException(nameof(name));

        public FormulaIdentifier Name { get; }
    }

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

    public sealed record Norm : Formula
    {
        public Norm(Formula operand) =>
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

    public sealed record Apply : Formula
    {
        public Apply(Formula function, ImmutableArray<Formula> arguments)
        {
            Function = FormulaLatexRules.RequireApplicableFunction(function, nameof(function));
            Arguments = RequireValues(arguments, nameof(arguments));
        }

        public Formula Function { get; }

        public ImmutableArray<Formula> Arguments { get; }
    }

    public sealed record TypeArrow : Formula
    {
        public TypeArrow(Formula domain, Formula codomain)
        {
            Domain = domain ?? throw new ArgumentNullException(nameof(domain));
            Codomain = codomain ?? throw new ArgumentNullException(nameof(codomain));
        }

        public Formula Domain { get; }

        public Formula Codomain { get; }
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

    public sealed record Logic : Formula
    {
        public Logic(Formula left, FormulaLogicOperator @operator, Formula right)
        {
            Left = left ?? throw new ArgumentNullException(nameof(left));
            Right = right ?? throw new ArgumentNullException(nameof(right));
            Operator = @operator is FormulaLogicOperator.And
                or FormulaLogicOperator.Or
                or FormulaLogicOperator.Implies
                or FormulaLogicOperator.Iff
                    ? @operator
                    : throw new ArgumentOutOfRangeException(nameof(@operator));
        }

        public Formula Left { get; }

        public FormulaLogicOperator Operator { get; }

        public Formula Right { get; }
    }

    public sealed record Not : Formula
    {
        public Not(Formula operand) =>
            Operand = operand ?? throw new ArgumentNullException(nameof(operand));

        public Formula Operand { get; }
    }

    public sealed record Bind : Formula
    {
        public Bind(
            FormulaQuantifier quantifier,
            FormulaIdentifier variable,
            Formula domain,
            Formula body)
        {
            Quantifier = quantifier is FormulaQuantifier.ForAll or FormulaQuantifier.Exists
                ? quantifier
                : throw new ArgumentOutOfRangeException(nameof(quantifier));
            Variable = variable ?? throw new ArgumentNullException(nameof(variable));
            Domain = domain ?? throw new ArgumentNullException(nameof(domain));
            Body = body ?? throw new ArgumentNullException(nameof(body));
        }

        public FormulaQuantifier Quantifier { get; }

        public FormulaIdentifier Variable { get; }

        public Formula Domain { get; }

        public Formula Body { get; }
    }

    public sealed record BoundVariable
    {
        public BoundVariable(FormulaIdentifier name, Formula domain)
        {
            Name = name ?? throw new ArgumentNullException(nameof(name));
            Domain = domain ?? throw new ArgumentNullException(nameof(domain));
        }

        public FormulaIdentifier Name { get; }

        public Formula Domain { get; }
    }

    public sealed record BindMany : Formula
    {
        public BindMany(
            FormulaQuantifier quantifier,
            ImmutableArray<BoundVariable> variables,
            Formula body)
        {
            Quantifier = quantifier is FormulaQuantifier.ForAll or FormulaQuantifier.Exists
                ? quantifier
                : throw new ArgumentOutOfRangeException(nameof(quantifier));
            if (variables.IsDefaultOrEmpty || variables.Any(static value => value is null))
            {
                throw new ArgumentException(
                    "A formula binding requires at least one complete bound variable.",
                    nameof(variables));
            }

            Variables = variables;
            Body = body ?? throw new ArgumentNullException(nameof(body));
        }

        public FormulaQuantifier Quantifier { get; }

        public ImmutableArray<BoundVariable> Variables { get; }

        public Formula Body { get; }
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
            or FormulaRelationOperator.LessThan
            or FormulaRelationOperator.LessThanOrEqual
            or FormulaRelationOperator.GreaterThan
            or FormulaRelationOperator.GreaterThanOrEqual
            or FormulaRelationOperator.MemberOf
            or FormulaRelationOperator.Divides
            or FormulaRelationOperator.SubsetOf
            or FormulaRelationOperator.Equivalent
                ? value
                : throw new ArgumentOutOfRangeException(parameterName);
}
