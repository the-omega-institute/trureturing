using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.Text;

namespace StrataLint.Scribe;

public static class LatexWriter
{
    private const int RelationPrecedence = 10;
    private const int LogicPrecedence = 5;
    private const int AdditivePrecedence = 20;
    private const int MultiplicativePrecedence = 30;
    private const int PrefixPrecedence = 40;
    private const int ScriptPrecedence = 80;
    private const int AtomPrecedence = 100;

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static string Write(Formula formula) => Write(formula, "standalone formula");

    internal static string Write(Formula formula, string source)
    {
        ArgumentNullException.ThrowIfNull(formula);
        ArgumentException.ThrowIfNullOrWhiteSpace(source);
        var builder = new StringBuilder();
        WriteFormula(builder, formula, 0, source);
        ValidateRowBreakContinuations(builder, source);
        ValidateScriptChains(builder, source);
        return builder.ToString();
    }

    public static ImmutableArray<byte> WriteUtf8(Formula formula) =>
        ImmutableArray.CreateRange(StrictUtf8.GetBytes(Write(formula)));

    public static string WriteStatement(Formula formula) =>
        WriteStatement(formula, "standalone formula");

    internal static string WriteStatement(Formula formula, string source)
    {
        ArgumentNullException.ThrowIfNull(formula);
        ArgumentException.ThrowIfNullOrWhiteSpace(source);
        if (formula is not Formula.Layout layout)
        {
            return "$$" + Write(formula, source) + "$$";
        }

        var delimiter = layout.Mode == FormulaLayoutMode.Display ? "$$" : "$";
        return delimiter + Write(layout.Content, source) + delimiter;
    }

    private static void WriteFormula(
        StringBuilder builder,
        Formula formula,
        int parentPrecedence,
        string source)
    {
        var precedence = GetPrecedence(formula);
        var needsParentheses = precedence < parentPrecedence;
        if (needsParentheses)
        {
            builder.Append("\\left(");
        }

        switch (formula)
        {
            case Formula.Aligned aligned:
                builder.Append("\\begin{aligned}");
                for (var index = 0; index < aligned.Rows.Length; index++)
                {
                    if (index > 0)
                    {
                        builder.Append("\\\\");
                    }
                    WriteFormula(builder, aligned.Rows[index], 0, source);
                }
                builder.Append("\\end{aligned}");
                break;
            case Formula.LatexSequence sequence:
                WriteLatexItems(builder, sequence.Items, source);
                break;
            case Formula.LatexGroup group:
                builder.Append('{');
                WriteLatexItems(builder, group.Items, source);
                builder.Append('}');
                break;
            case Formula.LatexMacro macro:
                WriteLatexMacro(builder, macro.Value);
                break;
            case Formula.LatexSymbol symbol:
                builder.Append(symbol.Value switch
                {
                    FormulaLatexSymbol.Exclamation => '!', FormulaLatexSymbol.Ampersand => '&',
                    FormulaLatexSymbol.Apostrophe => '\'', FormulaLatexSymbol.OpenParenthesis => '(',
                    FormulaLatexSymbol.CloseParenthesis => ')', FormulaLatexSymbol.Asterisk => '*',
                    FormulaLatexSymbol.Plus => '+', FormulaLatexSymbol.Comma => ',',
                    FormulaLatexSymbol.Minus => '-', FormulaLatexSymbol.Period => '.',
                    FormulaLatexSymbol.Slash => '/', FormulaLatexSymbol.Colon => ':',
                    FormulaLatexSymbol.Semicolon => ';', FormulaLatexSymbol.LessThan => '<',
                    FormulaLatexSymbol.Equal => '=', FormulaLatexSymbol.GreaterThan => '>',
                    FormulaLatexSymbol.OpenBracket => '[', FormulaLatexSymbol.CloseBracket => ']',
                    FormulaLatexSymbol.Caret => '^', FormulaLatexSymbol.Underscore => '_',
                    FormulaLatexSymbol.VerticalBar => '|', _ => throw new UnreachableException(),
                });
                break;
            case Formula.LatexSpace:
                builder.Append(' ');
                break;
            case Formula.LatexNewline:
                builder.Append('\n');
                break;
            case Formula.LatexWord word:
                builder.Append(word.Value.Value);
                break;
            case Formula.LatexDigits digits:
                foreach (var digit in digits.Digits)
                {
                    builder.Append((char)('0' + digit));
                }
                break;
            case Formula.Layout layout:
                WriteFormula(builder, layout.Content, 0, source);
                break;
            case Formula.Symbol symbol:
                WriteIdentifier(builder, symbol.Name, false);
                break;
            case Formula.Number number:
                builder.Append(number.Value.ToString(CultureInfo.InvariantCulture));
                break;
            case Formula.Phi:
                builder.Append("\\varphi");
                break;
            case Formula.Psi:
                builder.Append("\\psi");
                break;
            case Formula.Placeholder:
                builder.Append("\\mathord{\\cdot}");
                break;
            case Formula.Integers:
                builder.Append("\\mathbb{Z}");
                break;
            case Formula.NamedConstant constant:
                builder.Append("\\mathrm{").Append(constant.Name.Value).Append('}');
                break;
            case Formula.Negate negate:
                builder.Append('-');
                WriteFormula(builder, negate.Operand, PrefixPrecedence, source);
                break;
            case Formula.Absolute absolute:
                builder.Append("\\left|");
                WriteFormula(builder, absolute.Operand, 0, source);
                builder.Append("\\right|");
                break;
            case Formula.Norm norm:
                builder.Append("\\left\\lVert ");
                WriteFormula(builder, norm.Operand, 0, source);
                builder.Append(" \\right\\rVert");
                break;
            case Formula.Binary binary:
                WriteBinary(builder, binary, source);
                break;
            case Formula.Fraction fraction:
                builder.Append("\\frac{");
                WriteFormula(builder, fraction.Numerator, 0, source);
                builder.Append("}{");
                WriteFormula(builder, fraction.Denominator, 0, source);
                builder.Append('}');
                break;
            case Formula.Subscript subscript:
                WriteFormula(
                    builder,
                    subscript.Base,
                    ProducesScript(subscript.Base)
                        ? AtomPrecedence + 1
                        : ScriptPrecedence,
                    source);
                builder.Append("_{");
                WriteFormula(builder, subscript.Index, 0, source);
                builder.Append('}');
                break;
            case Formula.Power power:
                WriteFormula(
                    builder,
                    power.Base,
                    ProducesScript(power.Base)
                        ? AtomPrecedence + 1
                        : ScriptPrecedence,
                    source);
                builder.Append("^{");
                WriteFormula(builder, power.Exponent, 0, source);
                builder.Append('}');
                break;
            case Formula.Floor floor:
                builder.Append("\\left\\lfloor");
                WriteFormula(builder, floor.Operand, 0, source);
                builder.Append("\\right\\rfloor");
                break;
            case Formula.Log log:
                builder.Append("\\log_{");
                WriteFormula(builder, log.Base, 0, source);
                builder.Append("}\\left(");
                WriteFormula(builder, log.Argument, 0, source);
                builder.Append("\\right)");
                break;
            case Formula.Modulo modulo:
                WriteFormula(builder, modulo.Value, MultiplicativePrecedence, source);
                builder.Append(" \\bmod ");
                WriteFormula(builder, modulo.Modulus, MultiplicativePrecedence + 1, source);
                break;
            case Formula.Sequence sequence:
                builder.Append("\\left(");
                WriteFormula(builder, sequence.Element, 0, source);
                builder.Append("\\right)_{");
                WriteFormula(builder, sequence.Index, 0, source);
                builder.Append(" \\in ");
                WriteFormula(builder, sequence.Domain, 0, source);
                builder.Append('}');
                break;
            case Formula.SetLiteral set:
                builder.Append("\\left\\{");
                WriteList(builder, set.Elements, source);
                builder.Append("\\right\\}");
                break;
            case Formula.SetBuilder setBuilder:
                builder.Append("\\left\\{");
                WriteFormula(builder, setBuilder.Element, 0, source);
                builder.Append(" \\mid ");
                WriteFormula(builder, setBuilder.Variable, 0, source);
                builder.Append(" \\in ");
                WriteFormula(builder, setBuilder.Domain, 0, source);
                builder.Append("\\right\\}");
                break;
            case Formula.FunctionCall function:
                WriteIdentifier(builder, function.Name, true);
                builder.Append("\\left(");
                WriteList(builder, function.Arguments, source);
                builder.Append("\\right)");
                break;
            case Formula.Apply application:
                WriteFormula(builder, application.Function, AtomPrecedence, source);
                builder.Append("\\left(");
                WriteList(builder, application.Arguments, source);
                builder.Append("\\right)");
                break;
            case Formula.TypeArrow arrow:
                WriteFormula(builder, arrow.Domain, RelationPrecedence + 1, source);
                builder.Append(" \\to ");
                WriteFormula(builder, arrow.Codomain, RelationPrecedence + 1, source);
                break;
            case Formula.Relation relation:
                WriteRelation(builder, relation, source);
                break;
            case Formula.RelationChain relationChain:
                WriteRelationChain(builder, relationChain, source);
                break;
            case Formula.Logic logic:
                WriteLogic(builder, logic, source);
                break;
            case Formula.Not not:
                builder.Append("\\neg ");
                WriteFormula(builder, not.Operand, LogicPrecedence + 1, source);
                break;
            case Formula.Bind bind:
                builder.Append(bind.Quantifier == FormulaQuantifier.ForAll
                    ? "\\forall "
                    : "\\exists ");
                builder.Append(bind.Variable.Value).Append(" \\in ");
                WriteFormula(builder, bind.Domain, LogicPrecedence + 1, source);
                builder.Append(",\\; ");
                WriteFormula(builder, bind.Body, LogicPrecedence, source);
                break;
            case Formula.BindMany bind:
                builder.Append(bind.Quantifier == FormulaQuantifier.ForAll
                    ? "\\forall "
                    : "\\exists ");
                for (var index = 0; index < bind.Variables.Length; index++)
                {
                    if (index > 0)
                    {
                        builder.Append(", ");
                    }
                    builder.Append(bind.Variables[index].Name.Value).Append(" \\in ");
                    WriteFormula(
                        builder,
                        bind.Variables[index].Domain,
                        LogicPrecedence + 1,
                        source);
                }
                builder.Append(",\\; ");
                WriteFormula(builder, bind.Body, LogicPrecedence, source);
                break;
            default:
                throw new UnreachableException("Unknown formula node.");
        }

        if (needsParentheses)
        {
            builder.Append("\\right)");
        }
    }

    private static void WriteLatexItems(
        StringBuilder builder,
        ImmutableArray<Formula> items,
        string source)
    {
        foreach (var item in items)
        {
            var boundary = builder.Length;
            WriteFormula(builder, item, 0, source);
            ValidateControlWordBoundary(builder, boundary, source);
        }
    }

    private static void ValidateControlWordBoundary(
        StringBuilder builder,
        int boundary,
        string source)
    {
        if (boundary == 0
            || boundary == builder.Length
            || !IsAsciiLetter(builder[boundary]))
        {
            return;
        }

        var controlWordStart = boundary;
        while (controlWordStart > 0 && IsAsciiLetter(builder[controlWordStart - 1]))
        {
            controlWordStart--;
        }
        if (controlWordStart == boundary
            || controlWordStart == 0
            || builder[controlWordStart - 1] != '\\')
        {
            return;
        }

        var successorEnd = boundary;
        while (successorEnd < builder.Length
            && IsAsciiLetterOrDigit(builder[successorEnd]))
        {
            successorEnd++;
        }
        var mergedMacroEnd = boundary;
        while (mergedMacroEnd < builder.Length && IsAsciiLetter(builder[mergedMacroEnd]))
        {
            mergedMacroEnd++;
        }

        var controlWord = builder.ToString(controlWordStart, boundary - controlWordStart);
        var successor = builder.ToString(boundary, successorEnd - boundary);
        var mergedMacro = builder.ToString(
            controlWordStart - 1,
            mergedMacroEnd - controlWordStart + 1);
        throw new InvalidOperationException(
            $"Formula emission rejected at {source}: control word '{controlWord}' is immediately "
            + $"followed by identifier '{successor}'; emitted bytes would form invalid LaTeX "
            + $"macro '{mergedMacro}'. Insert FormulaDsl.Sp to state the intended boundary.");
    }

    private static void ValidateRowBreakContinuations(StringBuilder builder, string source)
    {
        for (var index = 2; index < builder.Length; index++)
        {
            if (builder[index] != '['
                || builder[index - 1] != '\\'
                || builder[index - 2] != '\\')
            {
                continue;
            }

            var excerptStart = Math.Max(0, index - 16);
            var excerptEnd = Math.Min(builder.Length, index + 17);
            var excerpt = builder
                .ToString(excerptStart, excerptEnd - excerptStart)
                .Replace("\r", "\\r", StringComparison.Ordinal)
                .Replace("\n", "\\n", StringComparison.Ordinal);
            var byteOffset = StrictUtf8.GetByteCount(builder.ToString(0, index));
            throw new InvalidOperationException(
                $"Formula emission rejected at {source}: '[' at byte offset {byteOffset} "
                + $"immediately follows a '\\\\' row separator (excerpt '{excerpt}'). "
                + "The bracket would be consumed as the optional row-spacing argument; "
                + "insert FormulaDsl.Grp() between the row separator and '[' to state the "
                + "intended boundary.");
        }
    }

    /// <summary>
    /// A TeX base carries at most one superscript and one subscript, so a second <c>^</c>
    /// (or <c>_</c>) on the same base is a parse error (KaTeX: "Double superscript"), not a
    /// nested script. The structured <see cref="Formula.Power"/> and
    /// <see cref="Formula.Subscript"/> nodes parenthesize a base that already carries a
    /// script, but the raw LaTeX escape hatch composes its scripted tail out of nested
    /// sequences, and that tail is only visible here, in the finished bytes.
    /// </summary>
    private static void ValidateScriptChains(StringBuilder builder, string source)
    {
        for (var index = 0; index < builder.Length; index++)
        {
            var mark = builder[index];
            if (mark is not ('^' or '_'))
            {
                continue;
            }

            var successor = SkipScriptArgument(builder, index + 1);
            if (successor >= builder.Length || builder[successor] != mark)
            {
                continue;
            }

            var excerptStart = Math.Max(0, index - 16);
            var excerptEnd = Math.Min(builder.Length, successor + 17);
            var excerpt = builder
                .ToString(excerptStart, excerptEnd - excerptStart)
                .Replace("\r", "\\r", StringComparison.Ordinal)
                .Replace("\n", "\\n", StringComparison.Ordinal);
            var byteOffset = StrictUtf8.GetByteCount(builder.ToString(0, successor));
            throw new InvalidOperationException(
                $"Formula emission rejected at {source}: '{mark}' at byte offset {byteOffset} "
                + $"scripts a base that already carries a '{mark}' script (excerpt "
                + $"'{excerpt}'). TeX binds one script mark per base and refuses the second; "
                + "wrap the scripted base in FormulaDsl.Grp() to state the intended nesting.");
        }
    }

    /// <summary>
    /// Advances past the argument a script mark binds, plus the whitespace TeX discards
    /// around it: a brace group, a control sequence, or a single character.
    /// </summary>
    private static int SkipScriptArgument(StringBuilder builder, int index)
    {
        index = SkipDiscardedSpace(builder, index);
        if (index >= builder.Length)
        {
            return index;
        }

        if (builder[index] != '{')
        {
            index = builder[index] == '\\'
                ? SkipControlSequence(builder, index)
                : index + 1;
            return SkipDiscardedSpace(builder, index);
        }

        var depth = 0;
        while (index < builder.Length)
        {
            var value = builder[index];
            if (value == '\\')
            {
                index = SkipControlSequence(builder, index);
                continue;
            }

            index++;
            if (value == '{')
            {
                depth++;
            }
            else if (value == '}' && --depth == 0)
            {
                break;
            }
        }

        return SkipDiscardedSpace(builder, index);
    }

    private static int SkipControlSequence(StringBuilder builder, int index)
    {
        var cursor = index + 1;
        if (cursor >= builder.Length)
        {
            return cursor;
        }

        if (!IsAsciiLetter(builder[cursor]))
        {
            return cursor + 1;
        }

        while (cursor < builder.Length && IsAsciiLetter(builder[cursor]))
        {
            cursor++;
        }

        return cursor;
    }

    private static int SkipDiscardedSpace(StringBuilder builder, int index)
    {
        while (index < builder.Length && builder[index] is ' ' or '\n' or '\r')
        {
            index++;
        }

        return index;
    }

    private static bool IsAsciiLetter(char value) =>
        value is >= 'A' and <= 'Z' or >= 'a' and <= 'z';

    private static bool IsAsciiLetterOrDigit(char value) =>
        IsAsciiLetter(value) || value is >= '0' and <= '9';

    private static void WriteLatexMacro(StringBuilder builder, FormulaLatexMacro macro) =>
        builder.Append('\\').Append(LatexMacroName(macro));

    private static string LatexMacroName(FormulaLatexMacro macro) => macro switch
    {
        FormulaLatexMacro.Delta => "Delta",
        FormulaLatexMacro.Gamma => "Gamma",
        FormulaLatexMacro.Lambda => "Lambda",
        FormulaLatexMacro.Leftrightarrow => "Leftrightarrow",
        FormulaLatexMacro.Re => "Re",
        FormulaLatexMacro.Rightarrow => "Rightarrow",
        FormulaLatexMacro.Sigma => "Sigma",
        FormulaLatexMacro.Vert => "Vert",
        FormulaLatexMacro.Alpha => "alpha",
        FormulaLatexMacro.DeltaLower => "delta",
        FormulaLatexMacro.GammaLower => "gamma",
        FormulaLatexMacro.LambdaLower => "lambda",
        FormulaLatexMacro.SigmaLower => "sigma",
        FormulaLatexMacro.EscapedSpace => " ",
        FormulaLatexMacro.NegativeThinSpace => "!",
        FormulaLatexMacro.ThinSpace => ",",
        FormulaLatexMacro.SemicolonSpace => ";",
        FormulaLatexMacro.RowBreak => "\\",
        FormulaLatexMacro.OpenBrace => "{",
        FormulaLatexMacro.CloseBrace => "}",
        _ => macro.ToString().ToLowerInvariant(),
    };

    private static void WriteBinary(
        StringBuilder builder,
        Formula.Binary binary,
        string source)
    {
        var precedence = GetPrecedence(binary);
        WriteFormula(builder, binary.Left, precedence, source);
        builder.Append(binary.Operator switch
        {
            FormulaBinaryOperator.Add => " + ",
            FormulaBinaryOperator.Subtract => " - ",
            FormulaBinaryOperator.Multiply => " \\cdot ",
            _ => throw new UnreachableException("Unknown binary operator."),
        });
        var rightPrecedence = binary.Operator switch
        {
            FormulaBinaryOperator.Subtract => precedence + 1,
            FormulaBinaryOperator.Multiply when StartsWithNegation(binary.Right) =>
                GetPrecedence(binary.Right) + 1,
            _ => precedence,
        };
        WriteFormula(builder, binary.Right, rightPrecedence, source);
    }

    private static void WriteRelation(
        StringBuilder builder,
        Formula.Relation relation,
        string source)
    {
        WriteFormula(builder, relation.Left, RelationPrecedence + 1, source);
        builder.Append(relation.Operator switch
        {
            FormulaRelationOperator.Equal => " = ",
            FormulaRelationOperator.NotEqual => " \\ne ",
            FormulaRelationOperator.LessThan => " < ",
            FormulaRelationOperator.LessThanOrEqual => " \\le ",
            FormulaRelationOperator.GreaterThan => " > ",
            FormulaRelationOperator.GreaterThanOrEqual => " \\ge ",
            FormulaRelationOperator.MemberOf => " \\in ",
            FormulaRelationOperator.Divides => " \\mid ",
            FormulaRelationOperator.SubsetOf => " \\subseteq ",
            FormulaRelationOperator.Equivalent => " \\equiv ",
            _ => throw new UnreachableException("Unknown relation operator."),
        });
        WriteFormula(builder, relation.Right, RelationPrecedence + 1, source);
    }

    private static void WriteRelationChain(
        StringBuilder builder,
        Formula.RelationChain relation,
        string source)
    {
        for (var index = 0; index < relation.Operands.Length; index++)
        {
            if (index > 0)
            {
                builder.Append(relation.Operator switch
                {
                    FormulaRelationOperator.Equal => " = ",
                    FormulaRelationOperator.NotEqual => " \\ne ",
                    FormulaRelationOperator.LessThan => " < ",
                    FormulaRelationOperator.LessThanOrEqual => " \\le ",
                    FormulaRelationOperator.GreaterThan => " > ",
                    FormulaRelationOperator.GreaterThanOrEqual => " \\ge ",
                    FormulaRelationOperator.MemberOf => " \\in ",
                    FormulaRelationOperator.Divides => " \\mid ",
                    FormulaRelationOperator.SubsetOf => " \\subseteq ",
                    FormulaRelationOperator.Equivalent => " \\equiv ",
                    _ => throw new UnreachableException("Unknown relation operator."),
                });
            }

            WriteFormula(builder, relation.Operands[index], RelationPrecedence + 1, source);
        }
    }

    private static void WriteLogic(
        StringBuilder builder,
        Formula.Logic logic,
        string source)
    {
        WriteFormula(builder, logic.Left, LogicPrecedence + 1, source);
        builder.Append(logic.Operator switch
        {
            FormulaLogicOperator.And => " \\land ",
            FormulaLogicOperator.Or => " \\lor ",
            FormulaLogicOperator.Implies => " \\Rightarrow ",
            FormulaLogicOperator.Iff => " \\Leftrightarrow ",
            _ => throw new UnreachableException("Unknown logic operator."),
        });
        WriteFormula(builder, logic.Right, LogicPrecedence + 1, source);
    }

    private static void WriteIdentifier(
        StringBuilder builder,
        FormulaIdentifier identifier,
        bool function)
    {
        if (!function && identifier.Value.Length == 1)
        {
            builder.Append(identifier.Value);
            return;
        }

        builder.Append(function ? "\\operatorname{" : "\\mathit{");
        builder.Append(identifier.Value).Append('}');
    }

    private static void WriteList(
        StringBuilder builder,
        ImmutableArray<Formula> values,
        string source)
    {
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0)
            {
                builder.Append(", ");
            }

            WriteFormula(builder, values[index], 0, source);
        }
    }

    private static int GetPrecedence(Formula formula) => formula switch
    {
        Formula.Logic or Formula.Not or Formula.Bind or Formula.BindMany => LogicPrecedence,
        Formula.Relation or Formula.RelationChain or Formula.TypeArrow => RelationPrecedence,
        Formula.Binary { Operator: FormulaBinaryOperator.Add or FormulaBinaryOperator.Subtract } =>
            AdditivePrecedence,
        Formula.Binary => MultiplicativePrecedence,
        Formula.Modulo => MultiplicativePrecedence,
        Formula.Negate => PrefixPrecedence,
        Formula.Subscript or Formula.Power => ScriptPrecedence,
        _ => AtomPrecedence,
    };

    private static bool ProducesScript(Formula formula) =>
        formula is Formula.Subscript or Formula.Power or Formula.Sequence;

    private static bool StartsWithNegation(Formula formula) => formula switch
    {
        Formula.Negate => true,
        Formula.Binary { Operator: FormulaBinaryOperator.Multiply } binary =>
            StartsWithNegation(binary.Left),
        Formula.Modulo modulo => StartsWithNegation(modulo.Value),
        _ => false,
    };
}
