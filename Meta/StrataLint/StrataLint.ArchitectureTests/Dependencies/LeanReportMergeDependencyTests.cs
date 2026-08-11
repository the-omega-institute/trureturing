using System.Reflection;
using System.Reflection.Emit;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class LeanReportMergeDependencyTests
{
    [Fact]
    public void MergeCommandReachableTypesExcludeScribeAssembly()
    {
        var run = typeof(StrataLint.Cli.LeanReportMergeCommand).GetMethod(
            "Run", BindingFlags.Static | BindingFlags.NonPublic)
            ?? throw new MissingMethodException("LeanReportMergeCommand.Run");

        var assemblies = MethodBodyReachability.ApplicationAssemblies(run);

        Assert.Contains("StrataLint", assemblies);
        Assert.Contains("StrataLint.Engine", assemblies);
        Assert.DoesNotContain("StrataLint.Scribe", assemblies);
    }

    [Fact]
    public void ReachabilityGuardRejectsAScribeCallFixture()
    {
        var fixture = typeof(LeanReportMergeDependencyTests).GetMethod(
            nameof(ReachableScribeCall), BindingFlags.Static | BindingFlags.NonPublic)
            ?? throw new MissingMethodException(nameof(ReachableScribeCall));

        Assert.Contains(
            "StrataLint.Scribe",
            MethodBodyReachability.ApplicationAssemblies(fixture));
    }

    private static void ReachableScribeCall() => GC.KeepAlive(typeof(ScribeEmitter));
}

internal static class MethodBodyReachability
{
    private static readonly OpCode[] OneByteOpCodes = new OpCode[0x100];
    private static readonly OpCode[] TwoByteOpCodes = new OpCode[0x100];

    static MethodBodyReachability()
    {
        foreach (var field in typeof(OpCodes).GetFields(BindingFlags.Public | BindingFlags.Static))
        {
            if (field.GetValue(null) is not OpCode opcode) continue;
            var value = unchecked((ushort)opcode.Value);
            if (value < 0x100) OneByteOpCodes[value] = opcode;
            else if ((value & 0xff00) == 0xfe00) TwoByteOpCodes[value & 0xff] = opcode;
        }
    }

    internal static string[] ApplicationAssemblies(MethodBase entrypoint)
    {
        var assemblies = new HashSet<string>(StringComparer.Ordinal);
        var visited = new HashSet<MethodBase>();
        var pending = new Queue<MethodBase>();
        pending.Enqueue(entrypoint);

        while (pending.TryDequeue(out var method))
        {
            if (!visited.Add(method)) continue;
            AddType(method.DeclaringType, assemblies);
            AddType((method as MethodInfo)?.ReturnType, assemblies);
            foreach (var parameter in method.GetParameters()) AddType(parameter.ParameterType, assemblies);

            var bytes = method.GetMethodBody()?.GetILAsByteArray();
            if (bytes is null) continue;
            Scan(method, bytes, pending, assemblies);
        }

        return assemblies.Order(StringComparer.Ordinal).ToArray();
    }

    private static void Scan(
        MethodBase context,
        byte[] bytes,
        Queue<MethodBase> pending,
        HashSet<string> assemblies)
    {
        for (var offset = 0; offset < bytes.Length;)
        {
            var first = bytes[offset++];
            var opcode = first == 0xfe ? TwoByteOpCodes[bytes[offset++]] : OneByteOpCodes[first];
            switch (opcode.OperandType)
            {
                case OperandType.InlineField:
                case OperandType.InlineMethod:
                case OperandType.InlineTok:
                case OperandType.InlineType:
                    var token = BitConverter.ToInt32(bytes, offset);
                    offset += 4;
                    AddMember(ResolveMember(context, token), pending, assemblies);
                    break;
                case OperandType.InlineSwitch:
                    var count = BitConverter.ToInt32(bytes, offset);
                    offset += 4 + (count * 4);
                    break;
                default:
                    offset += OperandSize(opcode.OperandType);
                    break;
            }
        }
    }

    private static MemberInfo ResolveMember(MethodBase context, int token) =>
        context.Module.ResolveMember(
            token,
            context.DeclaringType?.GetGenericArguments(),
            context.IsGenericMethod ? context.GetGenericArguments() : null)
        ?? throw new InvalidOperationException($"Unable to resolve IL token {token} in {context}.");

    private static void AddMember(
        MemberInfo member,
        Queue<MethodBase> pending,
        HashSet<string> assemblies)
    {
        AddType(member.DeclaringType, assemblies);
        switch (member)
        {
            case MethodBase method:
                if (IsApplication(method.DeclaringType?.Assembly)) pending.Enqueue(method);
                if (method is MethodInfo info) AddType(info.ReturnType, assemblies);
                foreach (var parameter in method.GetParameters()) AddType(parameter.ParameterType, assemblies);
                break;
            case FieldInfo field:
                AddType(field.FieldType, assemblies);
                break;
            case Type type:
                AddType(type, assemblies);
                break;
        }
    }

    private static void AddType(Type? type, HashSet<string> assemblies)
    {
        if (type is null) return;
        while (type.HasElementType) type = type.GetElementType()!;
        if (type.IsGenericType)
        {
            foreach (var argument in type.GetGenericArguments()) AddType(argument, assemblies);
        }
        var name = type.Assembly.GetName().Name;
        if (name is not null && IsApplication(type.Assembly)) assemblies.Add(name);
    }

    private static bool IsApplication(Assembly? assembly)
    {
        var name = assembly?.GetName().Name;
        return name is not null
            && (name == "StrataLint" || name.StartsWith("StrataLint.", StringComparison.Ordinal));
    }

    private static int OperandSize(OperandType operandType) => operandType switch
    {
        OperandType.InlineNone => 0,
        OperandType.ShortInlineBrTarget or OperandType.ShortInlineI or OperandType.ShortInlineVar => 1,
        OperandType.InlineVar => 2,
        OperandType.InlineBrTarget or OperandType.InlineI or OperandType.InlineSig
            or OperandType.InlineString or OperandType.ShortInlineR => 4,
        OperandType.InlineI8 or OperandType.InlineR => 8,
        _ => throw new InvalidOperationException($"Unhandled IL operand type {operandType}."),
    };
}
