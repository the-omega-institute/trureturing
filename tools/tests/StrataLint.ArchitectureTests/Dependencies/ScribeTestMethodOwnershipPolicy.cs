using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.CompilerServices;

namespace StrataLint.ArchitectureTests;

internal sealed record ScribeTestMethodOwnershipViolation(
    string TestAssembly,
    string TestClass,
    string TestMethod,
    bool TouchesDocuments,
    bool MustTouchDocuments);

internal sealed record ScribeTestMethodOwnershipReading(
    string TestAssembly,
    IReadOnlyList<string> DiscoveredTestMethods,
    int DeclaredTestMethods,
    int TouchesDocuments,
    int DoesNotTouchDocuments,
    IReadOnlyList<ScribeTestMethodOwnershipViolation> Violations);

internal static class ScribeTestMethodOwnershipPolicy
{
    private static readonly OpCode[] SingleByteOpCodes = BuildSingleByteOpCodes();
    private static readonly OpCode[] MultiByteOpCodes = BuildMultiByteOpCodes();

    internal static ScribeTestMethodOwnershipReading Inspect(
        Assembly testAssembly,
        Assembly documentsAssembly,
        bool mustTouchDocuments)
    {
        var tests = GetLoadableTypes(testAssembly)
            .SelectMany(static type => type.GetMethods(
                BindingFlags.Public
                | BindingFlags.NonPublic
                | BindingFlags.Instance
                | BindingFlags.Static
                | BindingFlags.DeclaredOnly))
            .Where(IsXunitTestMethod)
            .OrderBy(static method => method.DeclaringType?.FullName, StringComparer.Ordinal)
            .ThenBy(static method => method.Name, StringComparer.Ordinal)
            .ToArray();

        var touchesDocuments = new Dictionary<MethodInfo, bool>();
        foreach (var test in tests)
        {
            touchesDocuments.Add(
                test,
                TouchesAssemblyThroughSameAssemblyCallClosure(
                    test,
                    testAssembly,
                    documentsAssembly));
        }

        var violations = ProjectViolations(testAssembly, touchesDocuments, mustTouchDocuments);

        var touchingCount = touchesDocuments.Count(static pair => pair.Value);
        return new ScribeTestMethodOwnershipReading(
            testAssembly.GetName().Name ?? testAssembly.FullName ?? "<unknown>",
            tests.Select(Format).ToArray(),
            tests.Length,
            touchingCount,
            tests.Length - touchingCount,
            violations);
    }

    internal static IReadOnlyList<ScribeTestMethodOwnershipViolation> ProjectViolations(
        Assembly testAssembly,
        IReadOnlyDictionary<MethodInfo, bool> touchesDocuments,
        bool mustTouchDocuments) => touchesDocuments
            .Where(pair => pair.Value != mustTouchDocuments)
            .Select(pair => new ScribeTestMethodOwnershipViolation(
                testAssembly.GetName().Name ?? testAssembly.FullName ?? "<unknown>",
                pair.Key.DeclaringType?.FullName ?? "<unknown>",
                pair.Key.Name,
                pair.Value,
                mustTouchDocuments))
            .ToArray();

    internal static bool TouchesAssemblyThroughSameAssemblyCallClosure(
        MethodBase root,
        Assembly testAssembly,
        Assembly targetAssembly)
    {
        var pending = new Queue<MethodBase>();
        var visited = new HashSet<(Module Module, int Token)>();
        pending.Enqueue(root);

        while (pending.Count > 0)
        {
            var method = pending.Dequeue();
            if (!TryAddMethod(visited, method))
            {
                continue;
            }

            EnqueueStateMachine(method, testAssembly, pending);

            foreach (var reference in ReadMetadataReferences(method))
            {
                if (ReferenceAssembly(reference) == targetAssembly)
                {
                    return true;
                }

                if (reference is MethodBase calledMethod
                    && calledMethod.Module.Assembly == testAssembly)
                {
                    pending.Enqueue(calledMethod);
                }
            }
        }

        return false;
    }

    private static bool TryAddMethod(
        ISet<(Module Module, int Token)> visited,
        MethodBase method)
    {
        try
        {
            return visited.Add((method.Module, method.MetadataToken));
        }
        catch (InvalidOperationException)
        {
            throw new InvalidOperationException(
                $"Cannot inspect method without a metadata token: {Format(method)}.");
        }
    }

    private static void EnqueueStateMachine(
        MethodBase method,
        Assembly testAssembly,
        Queue<MethodBase> pending)
    {
        var stateMachineType = method
            .GetCustomAttributes<StateMachineAttribute>(inherit: false)
            .Select(static attribute => attribute.StateMachineType)
            .SingleOrDefault();

        if (stateMachineType?.Assembly != testAssembly)
        {
            return;
        }

        var moveNext = stateMachineType.GetMethod(
            "MoveNext",
            BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
        if (moveNext is null)
        {
            throw new InvalidOperationException(
                $"Compiler state machine {stateMachineType.FullName} has no MoveNext method.");
        }

        pending.Enqueue(moveNext);
    }

    private static IEnumerable<MemberInfo> ReadMetadataReferences(MethodBase method)
    {
        var body = method.GetMethodBody();
        if (body is null)
        {
            yield break;
        }

        var il = body.GetILAsByteArray()
            ?? throw new InvalidOperationException($"Cannot read IL for {Format(method)}.");
        var typeArguments = method.DeclaringType?.GetGenericArguments();
        var methodArguments = method.IsGenericMethod ? method.GetGenericArguments() : null;

        for (var offset = 0; offset < il.Length;)
        {
            var instructionOffset = offset;
            var opCode = ReadOpCode(il, ref offset, method);
            switch (opCode.OperandType)
            {
                case OperandType.InlineMethod:
                    yield return Resolve(
                        method,
                        instructionOffset,
                        ReadInt32(il, ref offset, method),
                        token => method.Module.ResolveMethod(token, typeArguments, methodArguments));
                    break;
                case OperandType.InlineField:
                    yield return Resolve(
                        method,
                        instructionOffset,
                        ReadInt32(il, ref offset, method),
                        token => method.Module.ResolveField(token, typeArguments, methodArguments));
                    break;
                case OperandType.InlineType:
                    yield return Resolve(
                        method,
                        instructionOffset,
                        ReadInt32(il, ref offset, method),
                        token => method.Module.ResolveType(token, typeArguments, methodArguments));
                    break;
                case OperandType.InlineTok:
                    yield return Resolve(
                        method,
                        instructionOffset,
                        ReadInt32(il, ref offset, method),
                        token => method.Module.ResolveMember(token, typeArguments, methodArguments));
                    break;
                case OperandType.InlineSwitch:
                    var targetCount = ReadInt32(il, ref offset, method);
                    Advance(il, ref offset, checked(targetCount * sizeof(int)), method);
                    break;
                default:
                    Advance(il, ref offset, OperandSize(opCode.OperandType), method);
                    break;
            }
        }
    }

    private static MemberInfo Resolve(
        MethodBase source,
        int instructionOffset,
        int token,
        Func<int, MemberInfo?> resolver)
    {
        try
        {
            return resolver(token)
                ?? throw new InvalidOperationException("The metadata resolver returned null.");
        }
        catch (Exception exception) when (exception is ArgumentException
            or BadImageFormatException
            or InvalidOperationException)
        {
            throw new InvalidOperationException(
                $"Cannot resolve metadata token 0x{token:X8} at IL offset "
                + $"0x{instructionOffset:X4} in {Format(source)}.",
                exception);
        }
    }

    private static Assembly? ReferenceAssembly(MemberInfo reference) => reference switch
    {
        Type type => type.Assembly,
        MethodBase method => method.DeclaringType?.Assembly ?? method.Module.Assembly,
        FieldInfo field => field.DeclaringType?.Assembly ?? field.Module.Assembly,
        _ => reference.Module.Assembly,
    };

    private static bool IsXunitTestMethod(MethodInfo method) => method
        .GetCustomAttributes(inherit: true)
        .Any(static attribute => attribute is FactAttribute or TheoryAttribute);

    private static Type[] GetLoadableTypes(Assembly assembly)
    {
        try
        {
            return assembly.GetTypes();
        }
        catch (ReflectionTypeLoadException exception)
        {
            throw new InvalidOperationException(
                $"Cannot load every type from {assembly.FullName}: "
                + string.Join(" | ", exception.LoaderExceptions
                    .Where(static item => item is not null)
                    .Select(static item => item!.Message)),
                exception);
        }
    }

    private static OpCode ReadOpCode(byte[] il, ref int offset, MethodBase method)
    {
        EnsureAvailable(il, offset, 1, method);
        var first = il[offset++];
        if (first != 0xFE)
        {
            return SingleByteOpCodes[first];
        }

        EnsureAvailable(il, offset, 1, method);
        return MultiByteOpCodes[il[offset++]];
    }

    private static int ReadInt32(byte[] il, ref int offset, MethodBase method)
    {
        EnsureAvailable(il, offset, sizeof(int), method);
        var value = BitConverter.ToInt32(il, offset);
        offset += sizeof(int);
        return value;
    }

    private static void Advance(byte[] il, ref int offset, int count, MethodBase method)
    {
        EnsureAvailable(il, offset, count, method);
        offset += count;
    }

    private static void EnsureAvailable(
        byte[] il,
        int offset,
        int count,
        MethodBase method)
    {
        if (count < 0 || offset < 0 || offset > il.Length - count)
        {
            throw new InvalidOperationException(
                $"Invalid IL while reading {Format(method)} at offset 0x{offset:X4}.");
        }
    }

    private static int OperandSize(OperandType operandType) => operandType switch
    {
        OperandType.InlineNone => 0,
        OperandType.ShortInlineBrTarget or OperandType.ShortInlineI or OperandType.ShortInlineVar => 1,
        OperandType.InlineVar => 2,
        OperandType.InlineBrTarget
            or OperandType.InlineI
            or OperandType.ShortInlineR
            or OperandType.InlineSig
            or OperandType.InlineString => 4,
        OperandType.InlineI8 or OperandType.InlineR => 8,
        _ => throw new InvalidOperationException($"Unsupported IL operand type {operandType}."),
    };

    private static OpCode[] BuildSingleByteOpCodes()
    {
        var result = new OpCode[0x100];
        foreach (var opCode in AllOpCodes().Where(static code => code.Size == 1))
        {
            result[(byte)opCode.Value] = opCode;
        }

        return result;
    }

    private static OpCode[] BuildMultiByteOpCodes()
    {
        var result = new OpCode[0x100];
        foreach (var opCode in AllOpCodes().Where(static code => code.Size == 2))
        {
            result[(byte)(opCode.Value & 0xFF)] = opCode;
        }

        return result;
    }

    private static IEnumerable<OpCode> AllOpCodes() => typeof(OpCodes)
        .GetFields(BindingFlags.Public | BindingFlags.Static)
        .Where(static field => field.FieldType == typeof(OpCode))
        .Select(static field => (OpCode)field.GetValue(null)!);

    private static string Format(MethodBase method) =>
        $"{method.DeclaringType?.FullName ?? "<unknown>"}.{method.Name}";
}
