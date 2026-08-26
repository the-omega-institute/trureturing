using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Scribe;

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
            var name = CanonicalLeanNameDecoder.DecodePrefix(text, position, out var consumed);
            position += consumed;
            return name;
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
        private static LeanExpr Expr(Parser parser) { var result = parser.Expr(); parser.End(); return result; }
        private static LeanLevel Level(Parser parser) { var result = parser.Level(); parser.End(); return result; }
    }
}

internal static class ProjectionNotation
{
    internal static readonly ImmutableDictionary<string, string> Entries = new Dictionary<string, string>(StringComparer.Ordinal)
    {
        ["Eq"] = "=", ["Ne"] = "!=", ["Not"] = "not", ["And"] = "and", ["Or"] = "or", ["Iff"] = "iff",
        ["Complex"] = "Complex", ["Real"] = "Real", ["Int"] = "Int", ["Nat"] = "Nat",
        ["Membership.mem"] = "in", ["norm"] = "norm", ["Exists"] = "exists",
        ["D5.S3.Weil.LabeledZeta.LedgerLength"] = "LedgerLength",
        ["D5.S3.Weil.LabeledZeta.criticalAbscissa"] = "criticalAbscissa",
        ["D5.S3.Weil.Convention.criticalAbscissa"] = "criticalAbscissa",
        ["D5.S3.Zeros.ScalingRegisterRigidity.applyRegister"] = "applyRegister",
        ["D5.S3.Weil.HalfDensity.halfDensityReading"] = "halfDensityReading",
        ["D5.S3.Weil.CriticalLine.halfDensityReading"] = "halfDensityReading",
        ["D5.S3.Weil.ReflectionLedger.scalingLedger"] = "scalingLedger",
        ["D5.S0.Conventions.TotalCode.TotalCode"] = "TotalCode",
        ["D5.S0.Conventions.TotalCode.TotalCode.data"] = "TotalCode.data",
        ["D5.S0.Conventions.TotalCode.TotalCode.rules"] = "TotalCode.rules",
        ["D5.S0.Conventions.TotalCode.TotalCode.ledger"] = "TotalCode.ledger",
        ["D5.S3.Zeros.ScalingRegisterRigidity.ScalingRegister"] = "ScalingRegister",
        ["D5.S3.Zeros.ScalingRegisterRigidity.AddressIndependent"] = "AddressIndependent",
        ["D5.S3.Zeros.ScalingRegisterRigidity.RealizesAt"] = "RealizesAt",
        ["AnalyticOnNhd"] = "AnalyticOnNhd", ["IsPreconnected"] = "IsPreconnected",
        ["Filter.EventuallyEq"] = "EventuallyEq", ["nhds"] = "nhds",
        ["Real.exp"] = "exp", ["Complex.exp"] = "exp", ["Complex.I"] = "I", ["Real.pi"] = "pi",
        ["Int.castAddHom"] = "castAddHom", ["Int.cast"] = "cast", ["Nat.cast"] = "cast",
        ["Complex.ofReal"] = "ofReal",
        ["DFunLike.coe"] = "coe", ["HMul.hMul"] = "multiply", ["HDiv.hDiv"] = "divide",
        ["Complex.re"] = "re",
        ["IsClosed"] = "IsClosed", ["IsCompact"] = "IsCompact", ["IsSeqCompact"] = "IsSeqCompact",
        ["setOf"] = "setOf", ["AddSubgroup"] = "AddSubgroup",
        ["ZMod"] = "ZMod",
        ["D5.S1.Dynamics.UniversalSolenoid.projection"] = "projection",
        ["Finset.sum"] = "sum", ["Finset.univ"] = "univ", ["Set.univ"] = "univ",
        ["Subtype"] = "Subtype", ["Subtype.val"] = "val",
        ["Fintype.card"] = "card",
    }.ToImmutableDictionary(StringComparer.Ordinal);
}

internal sealed record DenoiseRule(int DropPrefix, int? KeepLast = null, ImmutableArray<int> Keep = default);

internal static class ProjectionDenoiser
{
    internal static readonly ImmutableDictionary<string, DenoiseRule> Rules = new Dictionary<string, DenoiseRule>(StringComparer.Ordinal)
    {
        ["Eq"] = new(0, 2), ["Ne"] = new(0, 2), ["And"] = new(0, 2), ["Or"] = new(0, 2),
        ["Iff"] = new(0, 2), ["Not"] = new(0, 1), ["Exists"] = new(0, 2),
        ["Membership.mem"] = new(0, 2), ["norm"] = new(0, 1),
        ["OfNat.ofNat"] = new(0, null, [1]), ["Neg.neg"] = new(0, 1),
        ["DFunLike.coe"] = new(0, 2), ["HMul.hMul"] = new(0, 2), ["HDiv.hDiv"] = new(0, 2),
        ["Complex.re"] = new(0, 1),
        ["IsClosed"] = new(0, 1), ["IsCompact"] = new(0, 1), ["IsSeqCompact"] = new(0, 1),
        ["setOf"] = new(0, 1),
        ["AddSubgroup"] = new(0, null, [0]),
        ["ZMod"] = new(0),
        ["Finset.sum"] = new(0, 2),
        ["Finset.univ"] = new(0, 0),
        ["Set.univ"] = new(0, 0), ["Subtype"] = new(0, 2), ["Subtype.val"] = new(0, 1),
        ["Fintype.card"] = new(0, null, [0]),
        ["D5.S3.Weil.LabeledZeta.LedgerLength"] = new(0, 0),
        ["D5.S3.Weil.ReflectionLedger.scalingLedger"] = new(0, 3),
        ["D5.S3.Weil.CriticalLine.halfDensityReading"] = new(0, 3),
        ["D5.S0.Conventions.TotalCode.TotalCode"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.data"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.rules"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.ledger"] = new(3),
        ["D5.S3.Zeros.ScalingRegisterRigidity.applyRegister"] = new(3),
        ["D5.S3.Zeros.ScalingRegisterRigidity.ScalingRegister"] = new(2),
        ["D5.S3.Zeros.ScalingRegisterRigidity.AddressIndependent"] = new(1),
        ["D5.S3.Zeros.ScalingRegisterRigidity.RealizesAt"] = new(3),
        ["AnalyticOnNhd"] = new(0, 2), ["IsPreconnected"] = new(0, 1),
        ["Filter.EventuallyEq"] = new(0, 3), ["nhds"] = new(0, 1),
        ["Real.exp"] = new(0), ["Complex.exp"] = new(0), ["Int.castAddHom"] = new(0, null, [0]),
        ["Int.cast"] = new(0, 1), ["Nat.cast"] = new(0, 1), ["Complex.ofReal"] = new(0),
    }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static bool TryClean(string name, ImmutableArray<LeanExpr> arguments,
        out ImmutableArray<LeanExpr> cleaned)
    {
        var leaf = name.Split('.').Last();
        if (!Rules.TryGetValue(name, out var rule) && !Rules.TryGetValue(leaf, out rule))
        {
            cleaned = default;
            return false;
        }
        if (!rule.Keep.IsDefault)
        {
            if (rule.Keep.Any(index => index < 0 || index >= arguments.Length)) { cleaned = default; return false; }
            cleaned = rule.Keep.Select(index => arguments[index]).ToImmutableArray();
            return true;
        }
        if (rule.DropPrefix > arguments.Length) { cleaned = default; return false; }
        cleaned = arguments[rule.DropPrefix..];
        if (rule.KeepLast is int count)
        {
            if (count > cleaned.Length) { cleaned = default; return false; }
            cleaned = cleaned[^count..];
        }
        return true;
    }
}

internal abstract record ProjectionOutcome
{
    internal sealed record Projected(Formula Formula) : ProjectionOutcome;
    internal sealed record Unprojectable(string Reason) : ProjectionOutcome;
}

internal static class PropPiToImplicationRule
{
    private static readonly ImmutableHashSet<string> PropositionConstructors =
        ImmutableHashSet.Create(StringComparer.Ordinal,
            "Eq", "Ne", "Not", "And", "Or", "Iff", "Exists");

    internal static bool Matches(LeanExpr.Pi pi) =>
        pi.BinderInfo == "bd"
        && IsProposition(pi.Domain)
        && !ContainsBoundVariable(pi.Body, depth: 0);

    private static bool IsProposition(LeanExpr expression)
    {
        if (expression is LeanExpr.Metadata metadata)
            return IsProposition(metadata.Body);
        if (expression is LeanExpr.Pi pi)
            return IsProposition(pi.Body);
        if (expression is not LeanExpr.App)
            return false;

        var head = expression;
        while (head is LeanExpr.App app)
            head = app.Function;
        return head is LeanExpr.Constant constant
            && PropositionConstructors.Contains(constant.Name.Split('.').Last());
    }

    private static bool ContainsBoundVariable(LeanExpr expression, uint depth) => expression switch
    {
        LeanExpr.Bound bound => bound.Index == depth,
        LeanExpr.App app => ContainsBoundVariable(app.Function, depth)
            || ContainsBoundVariable(app.Argument, depth),
        LeanExpr.Lambda lambda => ContainsBoundVariable(lambda.Domain, depth)
            || ContainsBoundVariable(lambda.Body, checked(depth + 1)),
        LeanExpr.Pi pi => ContainsBoundVariable(pi.Domain, depth)
            || ContainsBoundVariable(pi.Body, checked(depth + 1)),
        LeanExpr.Let let => ContainsBoundVariable(let.Type, depth)
            || ContainsBoundVariable(let.Value, depth)
            || ContainsBoundVariable(let.Body, checked(depth + 1)),
        LeanExpr.Metadata metadata => ContainsBoundVariable(metadata.Body, depth),
        LeanExpr.Projection projection => ContainsBoundVariable(projection.Body, depth),
        _ => false
    };
}

internal static class StatementProjector
{
    internal static ProjectionOutcome Project(LeanExpr expression) => Project(expression, []);

    private static ProjectionOutcome Project(LeanExpr expression, ImmutableArray<Formula> variables)
    {
        if (expression is LeanExpr.Pi pi)
        {
            if (pi.BinderInfo is "bi" or "bs" or "bc") return Project(pi.Body, variables.Insert(0, new Formula.Placeholder()));
            if (PropPiToImplicationRule.Matches(pi))
            {
                var premise = Project(pi.Domain, variables);
                var conclusion = Project(pi.Body, variables.Insert(0, new Formula.Placeholder()));
                if (premise is ProjectionOutcome.Unprojectable premiseFailure) return premiseFailure;
                if (conclusion is ProjectionOutcome.Unprojectable conclusionFailure) return conclusionFailure;
                return new ProjectionOutcome.Projected(new Formula.Logic(
                    ((ProjectionOutcome.Projected)premise).Formula,
                    FormulaLogicOperator.Implies,
                    ((ProjectionOutcome.Projected)conclusion).Formula));
            }
            var domain = Project(pi.Domain, variables);
            var identifier = FormulaIdentifier.Create("x" + variables.Length);
            var symbol = new Formula.Symbol(identifier);
            var body = Project(pi.Body, variables.Insert(0, symbol));
            if (domain is ProjectionOutcome.Unprojectable domainFailure) return domainFailure;
            if (body is ProjectionOutcome.Unprojectable bodyFailure) return bodyFailure;
            var d = (ProjectionOutcome.Projected)domain;
            var b = (ProjectionOutcome.Projected)body;
            return new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.ForAll, identifier, d.Formula, b.Formula));
        }

        if (expression is LeanExpr.Bound bound)
            return bound.Index < variables.Length
                ? new ProjectionOutcome.Projected(variables[(int)bound.Index])
                : new ProjectionOutcome.Unprojectable("unbound-bvar:" + bound.Index);
        if (expression is LeanExpr.Sort)
            return new ProjectionOutcome.Projected(new Formula.NamedConstant(FormulaIdentifier.Create("Type")));
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
        if (expression is LeanExpr.Lambda lambda)
        {
            var identifier = FormulaIdentifier.Create("x" + variables.Length);
            var body = Project(lambda.Body, variables.Insert(0, new Formula.Symbol(identifier)));
            return body is ProjectionOutcome.Projected projected
                ? new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.ForAll, identifier,
                    new Formula.NamedConstant(FormulaIdentifier.Create("Type")), projected.Formula))
                : body;
        }
        if (expression is LeanExpr.Projection projection)
        {
            var body = Project(projection.Body, variables);
            return body is ProjectionOutcome.Projected projected
                ? new ProjectionOutcome.Projected(new Formula.Apply(
                    new Formula.NamedConstant(FormulaIdentifier.Create(projection.Name.Split('.').Last())), [projected.Formula]))
                : body;
        }
        if (expression is LeanExpr.App)
        {
            var (head, arguments) = Flatten(expression);
            if (head is not LeanExpr.Constant headConstant)
            {
                var function = Project(head, variables);
                var projectedArguments = arguments.Select(argument => Project(argument, variables)).ToArray();
                var failure = projectedArguments.OfType<ProjectionOutcome.Unprojectable>().FirstOrDefault();
                if (function is ProjectionOutcome.Unprojectable functionFailure) return functionFailure;
                if (failure is not null) return failure;
                return new ProjectionOutcome.Projected(new Formula.Apply(
                    ((ProjectionOutcome.Projected)function).Formula,
                    projectedArguments.Cast<ProjectionOutcome.Projected>().Select(item => item.Formula).ToImmutableArray()));
            }
            if (!ProjectionDenoiser.TryClean(headConstant.Name, arguments, out var semanticArguments))
                return new ProjectionOutcome.Unprojectable("unregistered-elaboration-shape:" + headConstant.Name);
            var projected = semanticArguments.Select(argument => Project(argument, variables)).ToArray();
            var argumentFailure = projected.OfType<ProjectionOutcome.Unprojectable>().FirstOrDefault();
            if (argumentFailure is not null) return argumentFailure;
            var values = projected.Cast<ProjectionOutcome.Projected>().Select(item => item.Formula).ToArray();
            var leaf = headConstant.Name.Split('.').Last();
            if (leaf == "Eq" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.Equal, values[^1]));
            if (leaf == "Ne" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.NotEqual, values[^1]));
            if (leaf is "And" or "Or" or "Iff" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Logic(values[^2], leaf switch { "And" => FormulaLogicOperator.And, "Or" => FormulaLogicOperator.Or, _ => FormulaLogicOperator.Iff }, values[^1]));
            if (leaf == "Not" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Not(values[0]));
            if (leaf == "norm" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Norm(values[0]));
            if (leaf == "neg" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Negate(values[0]));
            if (headConstant.Name == "OfNat.ofNat" && values.Length == 1) return new ProjectionOutcome.Projected(values[0]);
            if (headConstant.Name == "DFunLike.coe" && values.Length == 2)
                return new ProjectionOutcome.Projected(new Formula.Apply(values[0], [values[1]]));
            if (headConstant.Name == "HMul.hMul" && values.Length == 2)
                return new ProjectionOutcome.Projected(new Formula.Binary(values[0], FormulaBinaryOperator.Multiply, values[1]));
            if (leaf == "mem" && values.Length == 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[0], FormulaRelationOperator.MemberOf, values[1]));
            if (leaf == "Exists" && semanticArguments.Length == 2 && semanticArguments[1] is LeanExpr.Lambda predicate)
            {
                var identifier = FormulaIdentifier.Create("x" + variables.Length);
                var domain = Project(semanticArguments[0], variables);
                var body = Project(predicate.Body, variables.Insert(0, new Formula.Symbol(identifier)));
                if (domain is ProjectionOutcome.Projected d && body is ProjectionOutcome.Projected b)
                    return new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.Exists, identifier, d.Formula, b.Formula));
            }
            if (!ProjectionNotation.Entries.TryGetValue(headConstant.Name, out var notation)
                && !ProjectionNotation.Entries.TryGetValue(leaf, out notation))
                return new ProjectionOutcome.Unprojectable("constant:" + headConstant.Name);
            var canonical = new string(notation.Where(char.IsLetterOrDigit).ToArray());
            var functionFormula = new Formula.NamedConstant(FormulaIdentifier.Create(canonical));
            return values.Length == 0
                ? new ProjectionOutcome.Projected(functionFormula)
                : new ProjectionOutcome.Projected(new Formula.Apply(functionFormula, values.ToImmutableArray()));
        }
        return new ProjectionOutcome.Unprojectable(
            "unregistered-elaboration-shape:" + expression.GetType().Name);
    }

    private static (LeanExpr Head, ImmutableArray<LeanExpr> Arguments) Flatten(LeanExpr expression)
    {
        var arguments = ImmutableArray.CreateBuilder<LeanExpr>();
        while (expression is LeanExpr.App app) { arguments.Insert(0, app.Argument); expression = app.Function; }
        return (expression, arguments.ToImmutable());
    }
}

internal static class StatementProjectionFixtureLoader
{
    private static bool TryReadModules(string reportPath, out JsonDocument document)
    {
        document = null!;
        try
        {
            var candidate = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            if (candidate.RootElement.ValueKind != JsonValueKind.Object
                || !candidate.RootElement.TryGetProperty("modules", out var modules)
                || modules.ValueKind != JsonValueKind.Array
                || !candidate.RootElement.TryGetProperty("schema", out var schema)
                || schema.ValueKind != JsonValueKind.String
                || schema.GetString() != RawLeanReportArtifact.Schema)
            {
                candidate.Dispose();
                return false;
            }

            document = candidate;
            return true;
        }
        catch (JsonException)
        {
            return false;
        }
    }

    internal const string ProjectorEpoch = "statement-projector-v1";
    internal sealed record Assessment(ProjectionOutcome Outcome, string DeclarationContentDigest);
    private static readonly AsyncLocal<string?> RepositoryRoot = new();
    private static readonly Dictionary<string, ImmutableDictionary<string, StatementEntry>> StatementsByRoot =
        new(StringComparer.Ordinal);
    private static readonly ConditionalWeakTable<Formula, LeanDeclarationRef> Derived = new();

    internal static Formula FromLean(LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var declarationName = declaration.Value.Replace('/', '.');
        var statements = StatementsForCurrentRepository();
        if (!statements.TryGetValue(declarationName, out var entry))
        {
            var matches = statements
                .Where(pair => pair.Key.EndsWith('.' + declaration.DeclarationName, StringComparison.Ordinal))
                .Select(static pair => pair.Value)
                .ToArray();
            if (matches.Length != 1)
                throw new InvalidOperationException($"Pinned statement-v1 fixture has no unique declaration: {declarationName}");
            entry = matches[0];
        }
        var encoded = entry!.Type;

        var formula = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type) switch
        {
            ProjectionOutcome.Projected projected => projected.Formula,
            ProjectionOutcome.Unprojectable failed => throw new InvalidOperationException(
                $"Pinned statement-v1 fixture is unprojectable for {declarationName}: {failed.Reason}"),
            _ => throw new InvalidOperationException("Unknown statement projection outcome.")
        };
        Derived.Add(formula, declaration);
        return formula;
    }

    internal static bool IsDerivedFrom(Formula formula, LeanDeclarationRef declaration) =>
        Derived.TryGetValue(formula, out var source)
        && string.Equals(source.Value, declaration.Value, StringComparison.Ordinal);

    internal static ProjectionOutcome Project(LeanDeclarationRef declaration)
        => Assess(declaration).Outcome;

    internal static Assessment Assess(LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var declarationName = declaration.Value.Replace('/', '.');
        var statements = StatementsForCurrentRepository();
        if (!statements.TryGetValue(declarationName, out var entry))
        {
            var matches = statements.Where(pair => pair.Key.EndsWith('.' + declaration.DeclarationName, StringComparison.Ordinal)).ToArray();
            if (matches.Length != 1)
            {
                var missing = "missing:" + declarationName;
                return new Assessment(
                    new ProjectionOutcome.Unprojectable(missing),
                    Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(missing))).ToLowerInvariant());
            }
            entry = matches[0].Value;
        }

        // The projector projects the declaration's *type*. For a theorem the type is the proposition,
        // so projecting it restates nothing the author owns. For a def, an inductive, or a structure the
        // type is only the signature — the defining body never reaches the projector — so a projected
        // statement there would present a signature as if it were the definition. Judge those
        // unprojectable, which leaves the author free to state the definition and records the gap.
        // The check sits after resolution so the short-name fallback above is covered too.
        if (!string.Equals(entry.Kind, "theorem", StringComparison.Ordinal))
        {
            var reason = "non-propositional-declaration:" + entry.Kind;
            return new Assessment(new ProjectionOutcome.Unprojectable(reason),
                Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(reason))).ToLowerInvariant());
        }

        var encoded = entry.Type;
        var digest = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(encoded))).ToLowerInvariant();
        try
        {
            return new Assessment(StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type), digest);
        }
        catch (FormatException exception)
        {
            return new Assessment(new ProjectionOutcome.Unprojectable(
                "unregistered-elaboration-shape:statement-v1-decoder:" + exception.Message), digest);
        }
    }

    internal static string ReasonCode(string reason) => reason.Split(':', 2)[0];
    internal static string OffendingSubject(string reason) =>
        reason.Contains(':', StringComparison.Ordinal) ? reason[(reason.IndexOf(':') + 1)..] : reason;

    internal static string FixtureDirectory(string repositoryRoot) => Path.Combine(
        repositoryRoot, "Golden", "Projection");

    internal static T WithRepositoryRoot<T>(string repositoryRoot, Func<T> action)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(action);
        var previous = RepositoryRoot.Value;
        RepositoryRoot.Value = Path.GetFullPath(repositoryRoot);
        try
        {
            return action();
        }
        finally
        {
            RepositoryRoot.Value = previous;
        }
    }

    private static ImmutableDictionary<string, StatementEntry> StatementsForCurrentRepository()
    {
        var repositoryRoot = RepositoryRoot.Value ?? FindRepositoryRoot();
        lock (StatementsByRoot)
        {
            if (!StatementsByRoot.TryGetValue(repositoryRoot, out var statements))
            {
                statements = LoadStatements(repositoryRoot);
                StatementsByRoot.Add(repositoryRoot, statements);
            }

            return statements;
        }
    }

    private static ImmutableDictionary<string, StatementEntry> LoadStatements(string repositoryRoot)
    {
        var fixtureDirectory = FixtureDirectory(repositoryRoot);
        var fixtures = new[]
        {
            (Name: "statement-projection-pilot-v1.json", Schema: "statement-projection-pilot-fixture-v1"),
            (Name: "statement-projection-expansion-v1.json", Schema: "statement-projection-expansion-fixture-v1")
        };
        var declarations = ImmutableDictionary.CreateBuilder<string, StatementEntry>(StringComparer.Ordinal);
        foreach (var fixtureSpec in fixtures)
        {
            var path = Path.Combine(fixtureDirectory, fixtureSpec.Name);
            if (!File.Exists(path))
            {
                throw new FileNotFoundException(
                    $"Projection fixture is missing from repository {repositoryRoot}: {path}",
                    path);
            }
            using var fixture = JsonDocument.Parse(File.ReadAllBytes(path));
            var schema = fixture.RootElement.GetProperty("schema").GetString();
            if (!string.Equals(schema, fixtureSpec.Schema, StringComparison.Ordinal))
                throw new FormatException($"Projection fixture schema mismatch: {path}");
            foreach (var declaration in fixture.RootElement.GetProperty("declarations").EnumerateArray())
            {
                var name = declaration.GetProperty("name").GetString()
                    ?? throw new FormatException($"Projection fixture has a null declaration name: {path}");
                var statement = declaration.GetProperty("type").GetString()
                    ?? throw new FormatException($"Projection fixture has a null statement-v1 value: {name}");
                // The kind is load-bearing, not decoration: the engineering CI job runs without a raw
                // Lean report and decides projectability from this file alone. A pinned entry whose kind
                // is absent would be judged differently in the two environments, so refuse to load it.
                var kind = declaration.TryGetProperty("kind", out var kindElement)
                    ? kindElement.GetString()
                    : throw new FormatException($"Projection fixture declaration has no kind: {name}");
                if (string.IsNullOrEmpty(kind))
                    throw new FormatException($"Projection fixture declaration has an empty kind: {name}");
                if (!declarations.TryAdd(name, new StatementEntry(statement, kind)))
                    throw new FormatException($"Duplicate projection fixture declaration: {name}");
            }
        }
        var reportPath = Path.Combine(repositoryRoot, ".lake", "build", "stratalint", "raw-lean-report.json");
        // File.Exists is not the same question as "is this a usable report". The engineering CI job
        // never produces one (that is lean-inspect's job), and tests running in parallel write their
        // own fixtures under the repository root, so this path can hold a partial or differently
        // shaped document. Reading it with GetProperty then threw KeyNotFoundException out of a
        // loader whose whole contract is "use the live report when there is one".
        if (File.Exists(reportPath) && TryReadModules(reportPath, out var reportDocument))
        {
            using var report = reportDocument;
            var reportDeclarations = report.RootElement.GetProperty("modules").EnumerateArray()
                .SelectMany(static module => module.GetProperty("declarations").EnumerateArray())
                .Select(static declaration =>
                {
                    var name = declaration.GetProperty("name").GetString()!;
                    var address = declaration.GetProperty("type_sha256").GetString()
                        ?? throw new FormatException($"Raw Lean report has a null type address: {name}");
                    var kind = declaration.TryGetProperty("kind", out var kindElement)
                        ? kindElement.GetString() ?? "unknown" : "unknown";
                    return (Name: name, Address: address, Kind: kind);
                })
                .ToArray();
            var loadMaterial = RawLeanReportArtifact.OpenStatementMaterialSource(
                reportPath,
                reportDeclarations.Select(static declaration => declaration.Address));
            foreach (var declaration in reportDeclarations)
            {
                declarations[declaration.Name] = new StatementEntry(
                    declaration.Kind,
                    () => loadMaterial(declaration.Address));
            }
        }
        return declarations.ToImmutable();
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(Environment.CurrentDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Golden", "Projection")))
                return directory.FullName;
        }
        throw new DirectoryNotFoundException(
            "Could not locate repository root containing Golden/Projection statement fixtures.");
    }
}

internal sealed class StatementEntry
{
    private readonly string? inlineType;
    private readonly Lazy<string>? material;

    internal StatementEntry(string type, string kind) =>
        (inlineType, Kind) = (type, kind);

    internal StatementEntry(string kind, Func<string> loadMaterial)
    {
        Kind = kind;
        material = new Lazy<string>(
            loadMaterial ?? throw new ArgumentNullException(nameof(loadMaterial)),
            LazyThreadSafetyMode.ExecutionAndPublication);
    }

    internal string Type => inlineType ?? material?.Value
        ?? throw new InvalidDataException("Statement projection has no material source.");

    internal string Kind { get; }
}
