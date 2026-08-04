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

    public static string Write(Formula formula)
    {
        ArgumentNullException.ThrowIfNull(formula);
        var builder = new StringBuilder();
        WriteFormula(builder, formula, 0);
        return builder.ToString();
    }

    public static ImmutableArray<byte> WriteUtf8(Formula formula) =>
        ImmutableArray.CreateRange(StrictUtf8.GetBytes(Write(formula)));

    public static string WriteStatement(Formula formula)
    {
        ArgumentNullException.ThrowIfNull(formula);
        if (formula is not Formula.Layout layout)
        {
            return "$$" + Write(formula) + "$$";
        }

        var delimiter = layout.Mode == FormulaLayoutMode.Display ? "$$" : "$";
        return delimiter + Write(layout.Content) + delimiter;
    }

    private static void WriteFormula(
        StringBuilder builder,
        Formula formula,
        int parentPrecedence)
    {
        var precedence = GetPrecedence(formula);
        var needsParentheses = precedence < parentPrecedence;
        if (needsParentheses)
        {
            builder.Append("\\left(");
        }

        switch (formula)
        {
            case Formula.TextRun text:
                builder.Append(text.Value);
                break;
            case Formula.AlignedRows aligned:
                builder.Append("\\begin{aligned}");
                for (var index = 0; index < aligned.Rows.Length; index++)
                {
                    if (index > 0)
                    {
                        builder.Append("\\\\");
                    }
                    builder.Append(aligned.Rows[index].Value);
                }
                builder.Append("\\end{aligned}");
                break;
            case Formula.Aligned aligned:
                builder.Append("\\begin{aligned}");
                for (var index = 0; index < aligned.Rows.Length; index++)
                {
                    if (index > 0)
                    {
                        builder.Append("\\\\");
                    }
                    WriteFormula(builder, aligned.Rows[index], 0);
                }
                builder.Append("\\end{aligned}");
                break;
            case Formula.LatexSequence sequence:
                foreach (var item in sequence.Items)
                {
                    WriteFormula(builder, item, 0);
                }
                break;
            case Formula.LatexGroup group:
                builder.Append('{');
                foreach (var item in group.Items)
                {
                    WriteFormula(builder, item, 0);
                }
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
                WriteFormula(builder, layout.Content, 0);
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
                WriteFormula(builder, negate.Operand, PrefixPrecedence);
                break;
            case Formula.Absolute absolute:
                builder.Append("\\left|");
                WriteFormula(builder, absolute.Operand, 0);
                builder.Append("\\right|");
                break;
            case Formula.Norm norm:
                builder.Append("\\left\\lVert ");
                WriteFormula(builder, norm.Operand, 0);
                builder.Append(" \\right\\rVert");
                break;
            case Formula.Binary binary:
                WriteBinary(builder, binary);
                break;
            case Formula.Fraction fraction:
                builder.Append("\\frac{");
                WriteFormula(builder, fraction.Numerator, 0);
                builder.Append("}{");
                WriteFormula(builder, fraction.Denominator, 0);
                builder.Append('}');
                break;
            case Formula.Subscript subscript:
                WriteFormula(
                    builder,
                    subscript.Base,
                    ProducesScript(subscript.Base)
                        ? AtomPrecedence + 1
                        : ScriptPrecedence);
                builder.Append("_{");
                WriteFormula(builder, subscript.Index, 0);
                builder.Append('}');
                break;
            case Formula.Power power:
                WriteFormula(
                    builder,
                    power.Base,
                    ProducesScript(power.Base)
                        ? AtomPrecedence + 1
                        : ScriptPrecedence);
                builder.Append("^{");
                WriteFormula(builder, power.Exponent, 0);
                builder.Append('}');
                break;
            case Formula.Floor floor:
                builder.Append("\\left\\lfloor");
                WriteFormula(builder, floor.Operand, 0);
                builder.Append("\\right\\rfloor");
                break;
            case Formula.Log log:
                builder.Append("\\log_{");
                WriteFormula(builder, log.Base, 0);
                builder.Append("}\\left(");
                WriteFormula(builder, log.Argument, 0);
                builder.Append("\\right)");
                break;
            case Formula.Modulo modulo:
                WriteFormula(builder, modulo.Value, MultiplicativePrecedence);
                builder.Append(" \\bmod ");
                WriteFormula(builder, modulo.Modulus, MultiplicativePrecedence + 1);
                break;
            case Formula.Sequence sequence:
                builder.Append("\\left(");
                WriteFormula(builder, sequence.Element, 0);
                builder.Append("\\right)_{");
                WriteFormula(builder, sequence.Index, 0);
                builder.Append(" \\in ");
                WriteFormula(builder, sequence.Domain, 0);
                builder.Append('}');
                break;
            case Formula.SetLiteral set:
                builder.Append("\\left\\{");
                WriteList(builder, set.Elements);
                builder.Append("\\right\\}");
                break;
            case Formula.SetBuilder setBuilder:
                builder.Append("\\left\\{");
                WriteFormula(builder, setBuilder.Element, 0);
                builder.Append(" \\mid ");
                WriteFormula(builder, setBuilder.Variable, 0);
                builder.Append(" \\in ");
                WriteFormula(builder, setBuilder.Domain, 0);
                builder.Append("\\right\\}");
                break;
            case Formula.FunctionCall function:
                WriteIdentifier(builder, function.Name, true);
                builder.Append("\\left(");
                WriteList(builder, function.Arguments);
                builder.Append("\\right)");
                break;
            case Formula.Apply application:
                WriteFormula(builder, application.Function, AtomPrecedence);
                builder.Append("\\left(");
                WriteList(builder, application.Arguments);
                builder.Append("\\right)");
                break;
            case Formula.TypeArrow arrow:
                WriteFormula(builder, arrow.Domain, RelationPrecedence + 1);
                builder.Append(" \\to ");
                WriteFormula(builder, arrow.Codomain, RelationPrecedence + 1);
                break;
            case Formula.Relation relation:
                WriteRelation(builder, relation);
                break;
            case Formula.RelationChain relationChain:
                WriteRelationChain(builder, relationChain);
                break;
            case Formula.Logic logic:
                WriteLogic(builder, logic);
                break;
            case Formula.Not not:
                builder.Append("\\neg ");
                WriteFormula(builder, not.Operand, LogicPrecedence + 1);
                break;
            case Formula.Bind bind:
                builder.Append(bind.Quantifier == FormulaQuantifier.ForAll
                    ? "\\forall "
                    : "\\exists ");
                builder.Append(bind.Variable.Value).Append(" \\in ");
                WriteFormula(builder, bind.Domain, LogicPrecedence + 1);
                builder.Append(",\\; ");
                WriteFormula(builder, bind.Body, LogicPrecedence);
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
                    WriteFormula(builder, bind.Variables[index].Domain, LogicPrecedence + 1);
                }
                builder.Append(",\\; ");
                WriteFormula(builder, bind.Body, LogicPrecedence);
                break;
            default:
                throw new UnreachableException("Unknown formula node.");
        }

        if (needsParentheses)
        {
            builder.Append("\\right)");
        }
    }

    private static void WriteLatexMacro(StringBuilder builder, FormulaLatexMacro macro)
    {
        var name = macro switch
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
        builder.Append('\\').Append(name);
    }

    private static void WriteBinary(StringBuilder builder, Formula.Binary binary)
    {
        var precedence = GetPrecedence(binary);
        WriteFormula(builder, binary.Left, precedence);
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
        WriteFormula(builder, binary.Right, rightPrecedence);
    }

    private static void WriteRelation(StringBuilder builder, Formula.Relation relation)
    {
        WriteFormula(builder, relation.Left, RelationPrecedence + 1);
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
        WriteFormula(builder, relation.Right, RelationPrecedence + 1);
    }

    private static void WriteRelationChain(
        StringBuilder builder,
        Formula.RelationChain relation)
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

            WriteFormula(builder, relation.Operands[index], RelationPrecedence + 1);
        }
    }

    private static void WriteLogic(StringBuilder builder, Formula.Logic logic)
    {
        WriteFormula(builder, logic.Left, LogicPrecedence + 1);
        builder.Append(logic.Operator switch
        {
            FormulaLogicOperator.And => " \\land ",
            FormulaLogicOperator.Or => " \\lor ",
            FormulaLogicOperator.Implies => " \\Rightarrow ",
            FormulaLogicOperator.Iff => " \\Leftrightarrow ",
            _ => throw new UnreachableException("Unknown logic operator."),
        });
        WriteFormula(builder, logic.Right, LogicPrecedence + 1);
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

    private static void WriteList(StringBuilder builder, ImmutableArray<Formula> values)
    {
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0)
            {
                builder.Append(", ");
            }

            WriteFormula(builder, values[index], 0);
        }
    }

    private static int GetPrecedence(Formula formula) => formula switch
    {
        Formula.Logic or Formula.Not or Formula.Bind => LogicPrecedence,
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
