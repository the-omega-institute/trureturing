using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;

namespace StrataLint.Scribe.Tests;

internal static class ScribeResourceStructuralComparer
{
    internal static bool Equal(object? expected, object? actual, out string difference)
    {
        var seen = new HashSet<(object Left, object Right)>(PairComparer.Instance);
        return Compare(expected, actual, "$", seen, out difference);
    }

    private static bool Compare(
        object? expected,
        object? actual,
        string path,
        ISet<(object Left, object Right)> seen,
        out string difference)
    {
        if (ReferenceEquals(expected, actual))
        {
            difference = string.Empty;
            return true;
        }

        if (expected is null || actual is null)
        {
            difference = path;
            return false;
        }

        var expectedType = expected.GetType();
        if (expectedType != actual.GetType())
        {
            difference = $"{path} type {expectedType.FullName}/{actual.GetType().FullName}";
            return false;
        }

        if (expected is string || expectedType.IsPrimitive || expectedType.IsEnum
            || expected is decimal or DateTime or DateTimeOffset or Guid)
        {
            if (Equals(expected, actual))
            {
                difference = string.Empty;
                return true;
            }

            difference = path;
            return false;
        }

        if (expected is IEnumerable expectedSequence && actual is IEnumerable actualSequence)
        {
            var left = expectedSequence.GetEnumerator();
            var right = actualSequence.GetEnumerator();
            var index = 0;
            while (true)
            {
                var hasLeft = left.MoveNext();
                var hasRight = right.MoveNext();
                if (!hasLeft || !hasRight)
                {
                    if (hasLeft == hasRight)
                    {
                        difference = string.Empty;
                        return true;
                    }

                    difference = $"{path}[{index}]";
                    return false;
                }

                if (!Compare(left.Current, right.Current, $"{path}[{index}]", seen, out difference))
                {
                    return false;
                }

                index++;
            }
        }

        if (!seen.Add((expected, actual)))
        {
            difference = string.Empty;
            return true;
        }

        foreach (var property in expectedType
            .GetProperties(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
            .Where(static property => property.GetIndexParameters().Length == 0 && property.GetMethod is not null)
            .OrderBy(static property => property.Name, StringComparer.Ordinal))
        {
            var left = Read(property, expected);
            var right = Read(property, actual);
            if (left.Fault is not null || right.Fault is not null)
            {
                if (left.Fault?.Equals(right.Fault) == true)
                {
                    continue;
                }

                difference = $"{path}.{property.Name}";
                return false;
            }

            if (!Compare(left.Value, right.Value, $"{path}.{property.Name}", seen, out difference))
            {
                return false;
            }
        }

        difference = string.Empty;
        return true;
    }

    private static (object? Value, PropertyFault? Fault) Read(PropertyInfo property, object instance)
    {
        try
        {
            return (property.GetValue(instance), null);
        }
        catch (Exception exception)
        {
            return (null, new PropertyFault(exception.GetType(), exception.Message));
        }
    }

    private sealed record PropertyFault(Type Type, string Message);

    private sealed class PairComparer : IEqualityComparer<(object Left, object Right)>
    {
        internal static readonly PairComparer Instance = new();

        public bool Equals((object Left, object Right) x, (object Left, object Right) y) =>
            ReferenceEquals(x.Left, y.Left) && ReferenceEquals(x.Right, y.Right);

        public int GetHashCode((object Left, object Right) value) =>
            HashCode.Combine(RuntimeHelpers.GetHashCode(value.Left), RuntimeHelpers.GetHashCode(value.Right));
    }
}

