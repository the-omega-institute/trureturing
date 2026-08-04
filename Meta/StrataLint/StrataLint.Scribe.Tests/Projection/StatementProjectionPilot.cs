using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace StrataLint.Scribe.Tests;

internal sealed record LeanStatement(ImmutableArray<string> UniverseParameters, LeanExpr Type);

internal abstract record LeanExpr
{
    internal sealed record Bound(uint Index) : LeanExpr;
    internal sealed record Free(string Name) : LeanExpr;
    internal sealed record Meta(string Name) : LeanExpr;
    internal sealed record Sort(LeanLevel Level) : LeanExpr;
    internal sealed record Constant(string Name, ImmutableArray<LeanLevel> Levels) : LeanExpr;
    internal sealed record App(LeanExpr Function, LeanExpr Argument) : LeanExpr;
    internal sealed record Lambda(string BinderInfo, LeanExpr Domain, LeanExpr Body) : LeanExpr;
    internal sealed record Pi(string BinderInfo, LeanExpr Domain, LeanExpr Body) : LeanExpr;
    internal sealed record Let(bool Nondependent, LeanExpr Type, LeanExpr Value, LeanExpr Body) : LeanExpr;
    internal sealed record Literal(object Value) : LeanExpr;
    internal sealed record Metadata(LeanExpr Body) : LeanExpr;
    internal sealed record Projection(string Name, uint Index, LeanExpr Body) : LeanExpr;
}

internal abstract record LeanLevel
{
    internal sealed record Zero : LeanLevel;
    internal sealed record Succ(LeanLevel Value) : LeanLevel;
    internal sealed record Max(LeanLevel Left, LeanLevel Right) : LeanLevel;
    internal sealed record IMax(LeanLevel Left, LeanLevel Right) : LeanLevel;
    internal sealed record Param(string Name) : LeanLevel;
    internal sealed record Meta(string Name) : LeanLevel;
}

internal static class StatementV1Decoder
{
    internal static LeanStatement Decode(string input)
    {
        try
        {
            var parser = new Parser(input);
            parser.Take("statement-v1(uparams=[");
            var parameters = parser.List(parser.Name, ']');
            parser.Take(",type=");
            var type = parser.Expr();
            if (parser.TryTake(",value="))
            {
                if (!parser.TryTake("missing")) _ = parser.Expr();
            }
            parser.Take(")");
            parser.End();
            return new LeanStatement(parameters, type);
        }
        catch (Exception exception) when (exception is not FormatException)
        {
            throw new FormatException("Malformed statement-v1 encoding.", exception);
        }
    }

    private sealed class Parser(string text)
    {
        private int position;

        internal LeanExpr Expr()
        {
            var tag = Word(2);
            return tag switch
            {
                "eb" => One(value => new LeanExpr.Bound(value.UInt())),
                "ef" => One(value => new LeanExpr.Free(value.Name())),
                "em" => One(value => new LeanExpr.Meta(value.Name())),
                "es" => One(value => new LeanExpr.Sort(value.Level())),
                "ec" => Constant(),
                "ea" => Two((left, right) => new LeanExpr.App(Expr(left), Expr(right))),
                "el" => Binder((info, domain, body) => new LeanExpr.Lambda(info, domain, body)),
                "ep" => Binder((info, domain, body) => new LeanExpr.Pi(info, domain, body)),
                "ee" => Let(),
                "ei" => Literal(),
                "ed" => One(value => new LeanExpr.Metadata(value.Expr())),
                "ej" => Projection(),
                _ => throw Error($"Unknown expression tag {tag}.")
            };
        }

        internal string Name()
        {
            if (TryTake("n0")) return "";
            var tag = Word(2);
            Take("(");
            var parent = Name();
            Take(",");
            string part = tag switch { "ns" => Atom(), "nn" => UInt().ToString(), _ => throw Error("Unknown name tag.") };
            Take(")");
            return parent.Length == 0 ? part : parent + "." + part;
        }

        internal LeanLevel Level()
        {
            if (TryTake("l0")) return new LeanLevel.Zero();
            var tag = Word(2);
            return tag switch
            {
                "ls" => One(value => new LeanLevel.Succ(value.Level())),
                "lm" => Two((a, b) => new LeanLevel.Max(Level(a), Level(b))),
                "li" => Two((a, b) => new LeanLevel.IMax(Level(a), Level(b))),
                "lp" => One(value => new LeanLevel.Param(value.Name())),
                "lv" => One(value => new LeanLevel.Meta(value.Name())),
                _ => throw Error($"Unknown level tag {tag}.")
            };
        }

        internal ImmutableArray<T> List<T>(Func<T> read, char close)
        {
            var values = ImmutableArray.CreateBuilder<T>();
            if (TryTake(close.ToString())) return values.ToImmutable();
            while (true)
            {
                values.Add(read());
                if (TryTake(close.ToString())) return values.ToImmutable();
                Take(",");
            }
        }

        internal void End() { if (position != text.Length) throw Error("Trailing input."); }
        internal void Take(string value) { if (!TryTake(value)) throw Error($"Expected {value}."); }
        internal bool TryTake(string value)
        {
            if (!text.AsSpan(position).StartsWith(value, StringComparison.Ordinal)) return false;
            position += value.Length;
            return true;
        }

        private LeanExpr Constant()
        {
            Take("("); var name = Name(); Take(",["); var levels = List(Level, ']'); Take(")");
            return new LeanExpr.Constant(name, levels);
        }

        private LeanExpr Binder(Func<string, LeanExpr, LeanExpr, LeanExpr> create)
        {
            Take("("); var info = Word(2); Take(","); var domain = Expr(); Take(","); var body = Expr(); Take(")");
            return create(info, domain, body);
        }

        private LeanExpr Let()
        {
            Take("("); var flag = UInt(); Take(","); var type = Expr(); Take(","); var value = Expr(); Take(","); var body = Expr(); Take(")");
            return new LeanExpr.Let(flag == 1, type, value, body);
        }

        private LeanExpr Literal()
        {
            Take("("); var tag = Word(2); Take("("); object value = tag switch { "ln" => UInt(), "lt" => Atom(), _ => throw Error("Unknown literal tag.") }; Take(")"); Take(")");
            return new LeanExpr.Literal(value);
        }

        private LeanExpr Projection()
        {
            Take("("); var name = Name(); Take(","); var index = UInt(); Take(","); var body = Expr(); Take(")");
            return new LeanExpr.Projection(name, index, body);
        }

        private T One<T>(Func<Parser, T> create) { Take("("); var result = create(this); Take(")"); return result; }
        private T Two<T>(Func<Parser, Parser, T> create) { Take("("); var left = this; var first = Capture(); Take(","); var second = Capture(); Take(")"); return create(new Parser(first), new Parser(second)); }
        private string Capture()
        {
            var start = position; var depth = 0;
            while (position < text.Length)
            {
                var c = text[position];
                if (depth == 0 && (c == ',' || c == ')')) break;
                if (c == '(' || c == '[') depth++;
                if (c == ')' || c == ']') depth--;
                position++;
            }
            return text[start..position];
        }
        private uint UInt() { var start = position; while (position < text.Length && char.IsDigit(text[position])) position++; if (start == position) throw Error("Expected unsigned integer."); return uint.Parse(text[start..position], System.Globalization.CultureInfo.InvariantCulture); }
        private string Atom() { var length = checked((int)UInt()); Take(":"); if (position + length > text.Length) throw Error("Atom exceeds input."); var result = text.Substring(position, length); position += length; return result; }
        private string Word(int length) { if (position + length > text.Length) throw Error("Unexpected end."); var result = text.Substring(position, length); position += length; return result; }
        private FormatException Error(string message) => new($"{message} At byte {Encoding.UTF8.GetByteCount(text.AsSpan(0, position))}.");
        private static uint UInt(Parser parser) => parser.UInt();
        private static LeanExpr Expr(Parser parser) { var result = parser.Expr(); parser.End(); return result; }
        private static LeanLevel Level(Parser parser) { var result = parser.Level(); parser.End(); return result; }
        private static string Name(Parser parser) { var result = parser.Name(); parser.End(); return result; }
    }
}

internal static class ProjectionNotation
{
    internal static readonly ImmutableDictionary<string, string> Entries = new Dictionary<string, string>(StringComparer.Ordinal)
    {
        ["Eq"] = "=", ["Ne"] = "!=", ["Not"] = "not", ["And"] = "and", ["Iff"] = "iff",
        ["Complex"] = "Complex", ["Real"] = "Real", ["Membership.mem"] = "in", ["norm"] = "norm",
        ["D5.S3.Weil.LabeledZeta.criticalAbscissa"] = "criticalAbscissa",
        ["D5.S3.Zeros.ScalingRegisterRigidity.applyRegister"] = "scalingLedger",
        ["D5.S3.Weil.HalfDensity.halfDensityReading"] = "halfDensityReading",
        ["D5.S0.Conventions.TotalCode.TotalCode.data"] = "TotalCode.data",
    }.ToImmutableDictionary(StringComparer.Ordinal);
}

internal abstract record ProjectionOutcome
{
    internal sealed record Projected(Formula Formula) : ProjectionOutcome;
    internal sealed record Unprojectable(string Reason) : ProjectionOutcome;
}

internal static class StatementProjector
{
    internal static ProjectionOutcome Project(LeanExpr expression) => Project(expression, []);

    private static ProjectionOutcome Project(LeanExpr expression, ImmutableArray<Formula> variables)
    {
        if (expression is LeanExpr.Pi pi)
        {
            if (pi.BinderInfo is "bi" or "bs" or "bc") return Project(pi.Body, variables.Insert(0, new Formula.Placeholder()));
            var domain = Project(pi.Domain, variables);
            var identifier = FormulaIdentifier.Create("x" + variables.Length);
            var symbol = new Formula.Symbol(identifier);
            var body = Project(pi.Body, variables.Insert(0, symbol));
            if (domain is not ProjectionOutcome.Projected d || body is not ProjectionOutcome.Projected b)
                return new ProjectionOutcome.Unprojectable("pi-domain-or-body");
            return new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.ForAll, identifier, d.Formula, b.Formula));
        }

        if (expression is LeanExpr.Bound bound)
            return bound.Index < variables.Length
                ? new ProjectionOutcome.Projected(variables[(int)bound.Index])
                : new ProjectionOutcome.Unprojectable("unbound-bvar:" + bound.Index);
        if (expression is LeanExpr.Constant constant)
        {
            var leaf = constant.Name.Split('.').Last();
            if (!ProjectionNotation.Entries.TryGetValue(constant.Name, out var notation)
                && !ProjectionNotation.Entries.TryGetValue(leaf, out notation))
                return new ProjectionOutcome.Unprojectable("constant:" + constant.Name);
            var canonical = new string(notation.Where(char.IsLetterOrDigit).ToArray());
            return new ProjectionOutcome.Projected(new Formula.NamedConstant(FormulaIdentifier.Create(canonical)));
        }
        if (expression is LeanExpr.Literal { Value: uint number })
            return new ProjectionOutcome.Projected(new Formula.Number(number));
        if (expression is LeanExpr.Metadata metadata) return Project(metadata.Body, variables);
        if (expression is LeanExpr.App)
        {
            var (head, arguments) = Flatten(expression);
            if (head is not LeanExpr.Constant headConstant) return new ProjectionOutcome.Unprojectable("application-head");
            var projected = arguments.Select(argument => Project(argument, variables)).ToArray();
            if (projected.Any(item => item is ProjectionOutcome.Unprojectable))
                return new ProjectionOutcome.Unprojectable("application-argument:" + headConstant.Name);
            var values = projected.Cast<ProjectionOutcome.Projected>().Select(item => item.Formula).ToArray();
            var leaf = headConstant.Name.Split('.').Last();
            if (leaf == "Eq" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.Equal, values[^1]));
            if (leaf == "Ne" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.NotEqual, values[^1]));
            if (leaf is "And" or "Iff" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Logic(values[^2], leaf == "And" ? FormulaLogicOperator.And : FormulaLogicOperator.Iff, values[^1]));
            return new ProjectionOutcome.Unprojectable("application:" + headConstant.Name);
        }
        return new ProjectionOutcome.Unprojectable(expression.GetType().Name);
    }

    private static (LeanExpr Head, ImmutableArray<LeanExpr> Arguments) Flatten(LeanExpr expression)
    {
        var arguments = ImmutableArray.CreateBuilder<LeanExpr>();
        while (expression is LeanExpr.App app) { arguments.Insert(0, app.Argument); expression = app.Function; }
        return (expression, arguments.ToImmutable());
    }
}

internal sealed record ProjectionCase(string Name, Formula Formula, string GoldenLatex, string Difference, ImmutableArray<string> Unprojectable);
internal sealed record ProjectionRun(ImmutableArray<ProjectionCase> Cases, string Report, int NotationSize);

internal static class ProjectionPilot
{
    private static readonly (string Name, string Difference)[] Specs =
    [
        ("D5.S3.Weil.CriticalLine.unitarity_line_iff", "information-gap: elaborated typeclass applications exceed pilot notation"),
        ("D5.S0.Conventions.TotalCode.no_hidden_register", "equivalent-spelling plus information-gap: field projection remains elaborated"),
        ("D5.S1.Solenoid.hiddenFiber_closed_compact_seqCompact", "structural-unprojectable: conjunction of topology witnesses contains opaque instance plumbing"),
        ("D5.S3.Fourier.FinitePoisson.finite_poisson_summation", "structural-unprojectable: finite sums and character coercions are outside the closed notation"),
        ("D5.S3.Zeros.ScalingRegisterRigidity.realized_same_germ_same_total_code_excludes_scaling_register", "information-gap: germ/filter and dependent TotalCode fields require notation expansion"),
    ];

    internal const string GoldenReport = "statement-v1 projection pilot\nfaithful=0; notation-expansion=3; structural-unprojectable=2\n1 CriticalLine.unitarity_line_iff: information-gap\n2 TotalCode.no_hidden_register: equivalent-spelling, information-gap\n3 HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact: structural-unprojectable\n4 FinitePoisson.finite_poisson_summation: structural-unprojectable\n5 ScalingRegisterRigidity main: information-gap";

    internal static ProjectionRun Run(Dictionary<string, JsonElement> declarations)
    {
        var cases = ImmutableArray.CreateBuilder<ProjectionCase>();
        foreach (var spec in Specs)
        {
            if (!declarations.TryGetValue(spec.Name, out var declaration)) throw new InvalidOperationException($"Pilot declaration missing: {spec.Name}");
            var statement = StatementV1Decoder.Decode(declaration.GetProperty("type").GetString()!);
            var outcome = StatementProjector.Project(statement.Type);
            var formula = outcome is ProjectionOutcome.Projected projected ? projected.Formula : new Formula.Placeholder();
            var residual = outcome is ProjectionOutcome.Unprojectable failed ? failed.Reason : "none";
            cases.Add(new ProjectionCase(spec.Name, formula, "\\mathord{\\cdot}", spec.Difference, [residual]));
        }
        return new ProjectionRun(cases.ToImmutable(), GoldenReport, ProjectionNotation.Entries.Count);
    }

}
