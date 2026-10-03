using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Scribe;

internal sealed partial class RelationSyntaxEvaluator
{
    private object? KnownValue(ExpressionSyntax expression, Dictionary<ISymbol, object?> scope, SyntaxNode owner)
    {
        var constant = Model(expression).GetConstantValue(expression);
        if (constant.HasValue && IsConstant(constant.Value)) return constant.Value;
        var symbol = Model(expression).GetSymbolInfo(expression).Symbol;
        if (symbol is not null && scope.TryGetValue(symbol, out var value) && value is Binding binding)
            return KnownValue(binding.Expression, binding.Scope, owner);
        try { return Eval(expression, scope); }
        catch (RelationSyntaxException)
        {
            throw Reject(owner, owner.Kind().ToString(), "Branch discriminant has no supported static value.");
        }
    }

    private static bool IsConstant(object? value) => value is null or string or char or bool
        or byte or sbyte or short or ushort or int or uint or long or ulong or float or double or decimal;

    private bool Condition(ExpressionSyntax expression, Dictionary<ISymbol, object?> scope, SyntaxNode owner)
    {
        bool Evaluate(ExpressionSyntax value) => Condition(value, scope, owner);
        if (Model(expression).GetOperation(expression) is IIsPatternOperation
            { Pattern: IConstantPatternOperation constantPattern } isPattern)
            return ConstantPattern(constantPattern, KnownValue((ExpressionSyntax)isPattern.Value.Syntax, scope, owner), owner);
        switch (expression)
        {
            case ParenthesizedExpressionSyntax parenthesized:
                return Evaluate(parenthesized.Expression);
            case PrefixUnaryExpressionSyntax prefix when prefix.IsKind(SyntaxKind.LogicalNotExpression):
                return !Evaluate(prefix.Operand);
            case BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.LogicalAndExpression):
                return Evaluate(binary.Left) && Evaluate(binary.Right);
            case BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.LogicalOrExpression):
                return Evaluate(binary.Left) || Evaluate(binary.Right);
            case BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.EqualsExpression)
                || binary.IsKind(SyntaxKind.NotEqualsExpression):
                var left = KnownValue(binary.Left, scope, owner);
                var right = KnownValue(binary.Right, scope, owner);
                if (!IsConstant(left) || !IsConstant(right)) break;
                if (Model(binary).GetOperation(binary) is not IBinaryOperation operation
                    || operation.OperatorMethod is { ContainingType.SpecialType: not (SpecialType.System_String or SpecialType.System_Decimal) }) break;
                left = ConvertConstant(left, operation.LeftOperand.Type, owner);
                right = ConvertConstant(right, operation.RightOperand.Type, owner);
                var equal = left switch
                {
                    double number when right is double other => number == other,
                    float number when right is float other => number == other,
                    _ => Equals(left, right),
                };
                return binary.IsKind(SyntaxKind.EqualsExpression) ? equal : !equal;
            case IsPatternExpressionSyntax pattern:
                var input = KnownValue(pattern.Expression, scope, owner);
                return Matches(pattern.Pattern, input, scope, owner);
            default:
                if (KnownValue(expression, scope, owner) is bool decision) return decision;
                break;
        }
        throw Reject(owner, owner.Kind().ToString(), "Branch condition is outside the closed constant set.");
    }

    private bool Matches(PatternSyntax pattern, object? input, Dictionary<ISymbol, object?> scope, SyntaxNode owner) => pattern switch
    {
        ConstantPatternSyntax constant when Model(constant).GetOperation(constant) is IConstantPatternOperation operation =>
            ConstantPattern(operation, input, owner),
        DiscardPatternSyntax => true,
        ParenthesizedPatternSyntax parenthesized => Matches(parenthesized.Pattern, input, scope, owner),
        BinaryPatternSyntax binary when binary.IsKind(SyntaxKind.OrPattern) =>
            Matches(binary.Left, input, scope, owner) || Matches(binary.Right, input, scope, owner),
        _ => throw Reject(owner, owner.Kind().ToString(), "Only constant, null and discard patterns are supported."),
    };

    private static bool ConstantPattern(IConstantPatternOperation pattern, object? input, SyntaxNode owner)
    {
        if (!pattern.Value.ConstantValue.HasValue)
            throw Reject(owner, owner.Kind().ToString(), "Pattern is not a compile-time constant.");
        var expected = pattern.Value.ConstantValue.Value;
        if (expected is null) return input is null;
        if (!IsConstant(input))
            throw Reject(owner, owner.Kind().ToString(), "Pattern input is outside the constant set.");
        return Equals(ConvertConstant(input, pattern.InputType, owner),
            ConvertConstant(expected, pattern.InputType, owner));
    }

    private static object? ConvertConstant(object? value, ITypeSymbol? type, SyntaxNode owner)
    {
        if (value is null) return null;
        if (type is INamedTypeSymbol { TypeKind: TypeKind.Enum } enumeration) type = enumeration.EnumUnderlyingType;
        try
        {
            return type?.SpecialType switch
            {
                SpecialType.System_SByte => Convert.ToSByte(value),
                SpecialType.System_Byte => Convert.ToByte(value),
                SpecialType.System_Int16 => Convert.ToInt16(value),
                SpecialType.System_UInt16 => Convert.ToUInt16(value),
                SpecialType.System_Int32 => Convert.ToInt32(value),
                SpecialType.System_UInt32 => Convert.ToUInt32(value),
                SpecialType.System_Int64 => Convert.ToInt64(value),
                SpecialType.System_UInt64 => Convert.ToUInt64(value),
                SpecialType.System_Single => Convert.ToSingle(value),
                SpecialType.System_Double => Convert.ToDouble(value),
                SpecialType.System_Decimal => Convert.ToDecimal(value),
                _ => value,
            };
        }
        catch (Exception exception) when (exception is InvalidCastException or OverflowException or FormatException)
        {
            throw Reject(owner, owner.Kind().ToString(), "Unsupported constant conversion.");
        }
    }

    private SwitchExpressionArmSyntax SwitchArm(SwitchExpressionSyntax selection, Dictionary<ISymbol, object?> scope)
    {
        var input = KnownValue(selection.GoverningExpression, scope, selection);
        if (!IsConstant(input)) throw Reject(selection, "SwitchExpression", "Switch value is not constant.");
        foreach (var arm in selection.Arms)
        {
            if (arm.WhenClause is not null)
                throw Reject(selection, "SwitchExpression", "Switch guards are outside the closed pattern set.");
            if (Matches(arm.Pattern, input, scope, selection)) return arm;
        }
        throw Reject(selection, "SwitchExpression", "No supported switch arm matched.");
    }

    private void ValidatePresentationEffects(SyntaxNode node, HashSet<ISymbol> visited,
        Dictionary<ISymbol, object?> scope, bool ignored = false, bool foldBranches = true)
    {
        ignored |= IsIgnoredPresentationCall(node);
        if (node is LocalFunctionStatementSyntax) return;
        if (node is BlockSyntax block)
        {
            var nested = new Dictionary<ISymbol, object?>(scope, SymbolEqualityComparer.Default);
            foreach (var statement in block.Statements)
            {
                ValidatePresentationEffects(statement, visited, nested, ignored, foldBranches);
                if (statement is LocalDeclarationStatementSyntax local)
                    foreach (var variable in local.Declaration.Variables)
                        if (variable.Initializer is { } initializer)
                            nested[Model(variable).GetDeclaredSymbol(variable)!] = new Binding(initializer.Value,
                                new(nested, SymbolEqualityComparer.Default));
                if (statement is ReturnStatementSyntax) break;
            }
            return;
        }
        SyntaxNode? selected = null;
        var selectedBranch = false;
        try
        {
            switch (foldBranches ? node : null)
            {
                case IfStatementSyntax conditional:
                    selected = Condition(conditional.Condition, scope, conditional)
                        ? conditional.Statement : conditional.Else?.Statement;
                    selectedBranch = true;
                    ValidatePresentationEffects(conditional.Condition, visited, scope, ignored, foldBranches);
                    break;
                case ConditionalExpressionSyntax conditional:
                    selected = Condition(conditional.Condition, scope, conditional)
                        ? conditional.WhenTrue : conditional.WhenFalse;
                    selectedBranch = true;
                    ValidatePresentationEffects(conditional.Condition, visited, scope, ignored, foldBranches);
                    break;
                case BinaryExpressionSyntax coalesce when coalesce.IsKind(SyntaxKind.CoalesceExpression):
                    selected = KnownValue(coalesce.Left, scope, coalesce) is null ? coalesce.Right : null;
                    selectedBranch = true;
                    ValidatePresentationEffects(coalesce.Left, visited, scope, ignored, foldBranches);
                    break;
                case SwitchExpressionSyntax selection:
                    selected = SwitchArm(selection, scope).Expression;
                    selectedBranch = true;
                    ValidatePresentationEffects(selection.GoverningExpression, visited, scope, ignored, foldBranches);
                    break;
            }
        }
        catch (RelationSyntaxException) when (!selectedBranch) { }
        if (selectedBranch)
        {
            if (selected is not null) ValidatePresentationEffects(selected, visited, scope, ignored, foldBranches);
            return;
        }
        if (node is AssignmentExpressionSyntax assignment && IsRelationWrite(assignment.Left, ignored))
            throw Reject(assignment, "IgnoredWrite", "Ignored source code may not write observable state.");
        if (node is PrefixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } prefix
            && IsRelationWrite(prefix.Operand, ignored))
            throw Reject(prefix, "IgnoredWrite", "Ignored source code may not write observable state.");
        if (node is PostfixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } postfix
            && IsRelationWrite(postfix.Operand, ignored))
            throw Reject(postfix, "IgnoredWrite", "Ignored source code may not write observable state.");
        if (node is ArgumentSyntax argument && argument.RefKindKeyword.RawKind != 0)
            throw Reject(argument, "IgnoredWrite", "By-reference source arguments may mutate observable state.");
        if (node is InvocationExpressionSyntax invocation
            && Model(invocation).GetSymbolInfo(invocation).Symbol is IMethodSymbol method)
        {
            if (ignored && !IsRecognizedInvocation(method))
                throw Reject(invocation, "IgnoredWrite", "Ignored source code may call only recognized pure operations.");
            if (method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } helper
                && helper is MethodDeclarationSyntax or LocalFunctionStatementSyntax && visited.Add(method))
            {
                var relationHelper = IsBranchValueType(method.ReturnType);
                try
                {
                    var mapped = Arguments(method, invocation.ArgumentList.Arguments, scope, invocation);
                    var nested = new Dictionary<ISymbol, object?>(SymbolEqualityComparer.Default);
                    foreach (var parameter in method.Parameters) nested[parameter] = mapped.GetValueOrDefault(parameter.Name);
                    if (helper is LocalFunctionStatementSyntax localHelper)
                    {
                        if (localHelper.ExpressionBody is { } expressionBody)
                            ValidatePresentationEffects(expressionBody, visited, nested, ignored, foldBranches && relationHelper);
                        if (localHelper.Body is { } body) ValidatePresentationEffects(body, visited, nested, ignored, foldBranches && relationHelper);
                    }
                    else ValidatePresentationEffects(helper, visited, nested, ignored, foldBranches && relationHelper);
                }
                finally { if (relationHelper) visited.Remove(method); }
            }
            if (method.ContainingType.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>"
                && method.Name is "Add" or "AddRange" or "Clear" or "Remove" or "RemoveAt"
                && method.ContainingType.TypeArguments.Any(IsRelationType))
                throw Reject(invocation, "IgnoredWrite", "Source code may mutate a relation collection.");
        }
        foreach (var child in node.ChildNodes()) ValidatePresentationEffects(child, visited, scope, ignored, foldBranches);
    }

    private static bool IsBranchValueType(ITypeSymbol type) => IsRelationType(type)
        || type is IArrayTypeSymbol array && IsBranchValueType(array.ElementType)
        || type.TypeKind == TypeKind.Enum
        || type.SpecialType is SpecialType.System_Boolean or SpecialType.System_Char
            or SpecialType.System_Byte or SpecialType.System_SByte or SpecialType.System_Int16
            or SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32
            or SpecialType.System_Int64 or SpecialType.System_UInt64 or SpecialType.System_Single
            or SpecialType.System_Double or SpecialType.System_Decimal;
}
