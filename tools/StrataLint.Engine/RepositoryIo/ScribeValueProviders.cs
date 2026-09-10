using Microsoft.CodeAnalysis;

namespace StrataLint.Engine;

// ExplicitValues v1's finite external provider contract. These exact native
// members consume in-memory values, ordinal/invariant formatting, or bound local
// callbacks/getters/enumerators. Their implementations and the child culture are
// material inputs. Source value types, record implementations, overrides,
// interfaces and value metadata remain
// owned by ScribeExecutionDependencies; this table cannot authorize an unbound
// value provider. No assembly, namespace, or additional overload is accepted.
// JSON is deliberately limited to text/value overloads (no streams, files,
// deserialization, custom converters or resolver configuration). Unsupported
// providers cause unfiltered project execution, even when framework-signed.
internal static class ScribeValueProviders
{
    internal static bool Supports(ISymbol symbol)
    {
        // Tuple fields are compiler-owned projections of already bound values.
        if (symbol is IFieldSymbol { ContainingType.IsTupleType: true }) return true;
        symbol = symbol is IMethodSymbol method ? ScribeCallableIndex.Normalize(method) : symbol.OriginalDefinition;
        return (symbol.ContainingAssembly.Name + ":" + symbol.GetDocumentationCommentId()) switch
        {
            "System.Collections.Immutable:F:System.Collections.Immutable.ImmutableArray`1.Empty" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.CreateBuilder``1" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.CreateRange``1(System.Collections.Generic.IEnumerable{``0})" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.Create``1(System.ReadOnlySpan{``0})" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.Create``1(``0)" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.Create``1(``0,``0)" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.Create``1(``0,``0,``0)" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.ToImmutableArray``1(System.Collections.Generic.IEnumerable{``0})" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray.ToImmutableArray``1(System.ReadOnlySpan{``0})" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray`1.AsSpan" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray`1.Builder.Add(`0)" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray`1.Builder.ToImmutable" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray`1.Enumerator.MoveNext" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableArray`1.GetEnumerator" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableHashSet.Create``1(System.Collections.Generic.IEqualityComparer{``0},System.ReadOnlySpan{``0})" or
            "System.Collections.Immutable:M:System.Collections.Immutable.ImmutableHashSet`1.Contains(`0)" or
            "System.Collections.Immutable:M:System.Linq.ImmutableArrayExtensions.Select``2(System.Collections.Immutable.ImmutableArray{``0},System.Func{``0,``1})" or
            "System.Collections.Immutable:M:System.Linq.ImmutableArrayExtensions.SequenceEqual``2(System.Collections.Immutable.ImmutableArray{``1},System.Collections.Immutable.ImmutableArray{``0},System.Collections.Generic.IEqualityComparer{``1})" or
            "System.Collections.Immutable:M:System.Linq.ImmutableArrayExtensions.ToDictionary``3(System.Collections.Immutable.ImmutableArray{``2},System.Func{``2,``0},System.Func{``2,``1},System.Collections.Generic.IEqualityComparer{``0})" or
            "System.Collections.Immutable:P:System.Collections.Immutable.ImmutableArray`1.Builder.Count" or
            "System.Collections.Immutable:P:System.Collections.Immutable.ImmutableArray`1.Enumerator.Current" or
            "System.Collections.Immutable:P:System.Collections.Immutable.ImmutableArray`1.IsDefault" or
            "System.Collections.Immutable:P:System.Collections.Immutable.ImmutableArray`1.Item(System.Int32)" or
            "System.Collections.Immutable:P:System.Collections.Immutable.ImmutableArray`1.Length" or
            "System.Collections:M:System.Collections.Generic.Dictionary`2.#ctor(System.Collections.Generic.IEqualityComparer{`0})" or
            "System.Collections:M:System.Collections.Generic.HashSet`1.#ctor(System.Collections.Generic.IEqualityComparer{`0})" or
            "System.Collections:M:System.Collections.Generic.HashSet`1.Add(`0)" or
            "System.Collections:M:System.Collections.Generic.HashSet`1.Contains(`0)" or
            "System.Collections:M:System.Collections.Generic.HashSet`1.Remove(`0)" or
            "System.Collections:M:System.Collections.Generic.HashSet`1.SetEquals(System.Collections.Generic.IEnumerable{`0})" or
            "System.Collections:M:System.Collections.Generic.List`1.#ctor" or
            "System.Collections:M:System.Collections.Generic.List`1.Add(`0)" or
            "System.Collections:M:System.Collections.Generic.List`1.Enumerator.MoveNext" or
            "System.Collections:M:System.Collections.Generic.List`1.GetEnumerator" or
            "System.Collections:M:System.Collections.Generic.Queue`1.#ctor(System.Collections.Generic.IEnumerable{`0})" or
            "System.Collections:M:System.Collections.Generic.Queue`1.Enqueue(`0)" or
            "System.Collections:M:System.Collections.Generic.Queue`1.TryDequeue(`0@)" or
            "System.Collections:P:System.Collections.Generic.Dictionary`2.Item(`0)" or
            "System.Collections:P:System.Collections.Generic.HashSet`1.Count" or
            "System.Collections:P:System.Collections.Generic.List`1.Enumerator.Current" or
            "System.Linq:M:System.Linq.Enumerable.Any``1(System.Collections.Generic.IEnumerable{``0},System.Func{``0,System.Boolean})" or
            "System.Linq:M:System.Linq.Enumerable.Count``1(System.Collections.Generic.IEnumerable{``0})" or
            "System.Linq:M:System.Linq.Enumerable.Distinct``1(System.Collections.Generic.IEnumerable{``0},System.Collections.Generic.IEqualityComparer{``0})" or
            "System.Linq:M:System.Linq.Enumerable.OrderByDescending``2(System.Collections.Generic.IEnumerable{``0},System.Func{``0,``1})" or
            "System.Linq:M:System.Linq.Enumerable.OrderBy``2(System.Collections.Generic.IEnumerable{``0},System.Func{``0,``1})" or
            "System.Linq:M:System.Linq.Enumerable.OrderBy``2(System.Collections.Generic.IEnumerable{``0},System.Func{``0,``1},System.Collections.Generic.IComparer{``1})" or
            "System.Linq:M:System.Linq.Enumerable.Order``1(System.Collections.Generic.IEnumerable{``0},System.Collections.Generic.IComparer{``0})" or
            "System.Linq:M:System.Linq.Enumerable.Range(System.Int32,System.Int32)" or
            "System.Linq:M:System.Linq.Enumerable.Select``2(System.Collections.Generic.IEnumerable{``0},System.Func{``0,System.Int32,``1})" or
            "System.Linq:M:System.Linq.Enumerable.Select``2(System.Collections.Generic.IEnumerable{``0},System.Func{``0,``1})" or
            "System.Linq:M:System.Linq.Enumerable.SequenceEqual``1(System.Collections.Generic.IEnumerable{``0},System.Collections.Generic.IEnumerable{``0})" or
            "System.Linq:M:System.Linq.Enumerable.ThenBy``2(System.Linq.IOrderedEnumerable{``0},System.Func{``0,``1},System.Collections.Generic.IComparer{``1})" or
            "System.Linq:M:System.Linq.Enumerable.ToArray``1(System.Collections.Generic.IEnumerable{``0})" or
            "System.Linq:M:System.Linq.Enumerable.Where``1(System.Collections.Generic.IEnumerable{``0},System.Func{``0,System.Boolean})" or
            "System.Memory:M:System.MemoryExtensions.AsSpan(System.String,System.Int32)" or
            "System.Memory:M:System.MemoryExtensions.SequenceEqual``1(System.ReadOnlySpan{``0},System.ReadOnlySpan{``0})" or
            "System.Memory:M:System.MemoryExtensions.StartsWith``1(System.ReadOnlySpan{``0},System.ReadOnlySpan{``0})" or
            "System.Runtime:F:System.Decimal.Zero" or
            "System.Runtime:F:System.Int32.MaxValue" or
            "System.Runtime:F:System.String.Empty" or
            "System.Runtime:F:System.StringComparison.Ordinal" or
            "System.Runtime:M:System.ArgumentNullException.ThrowIfNull(System.Object,System.String)" or
            "System.Runtime:M:System.Array.Empty``1" or
            "System.Runtime:M:System.Char.IsControl(System.Char)" or
            "System.Runtime:M:System.Collections.Generic.IEnumerable`1.GetEnumerator" or
            "System.Runtime:M:System.Collections.IEnumerable.GetEnumerator" or
            "System.Runtime:M:System.Collections.IEnumerator.MoveNext" or
            "System.Runtime:M:System.Convert.ToBase64String(System.ReadOnlySpan{System.Byte},System.Base64FormattingOptions)" or
            "System.Runtime:M:System.Convert.ToHexStringLower(System.ReadOnlySpan{System.Byte})" or
            "System.Runtime:M:System.Decimal.ToString(System.String,System.IFormatProvider)" or
            "System.Runtime:M:System.FormatException.#ctor(System.String)" or
            "System.Runtime:M:System.FormatException.#ctor(System.String,System.Exception)" or
            "System.Runtime:M:System.IDisposable.Dispose" or
            "System.Runtime:M:System.IO.IOException.#ctor(System.String)" or
            "System.Runtime:M:System.Index.op_Implicit(System.Int32)~System.Index" or
            "System.Runtime:M:System.Int32.ToString(System.IFormatProvider)" or
            "System.Runtime:M:System.InvalidOperationException.#ctor(System.String)" or
            "System.Runtime:M:System.ReadOnlySpan`1.Enumerator.MoveNext" or
            "System.Runtime:M:System.ReadOnlySpan`1.GetEnumerator" or
            "System.Runtime:M:System.String.#ctor(System.Char,System.Int32)" or
            "System.Runtime:M:System.String.CompareOrdinal(System.String,System.String)" or
            "System.Runtime:M:System.String.Contains(System.Char,System.StringComparison)" or
            "System.Runtime:M:System.String.EndsWith(System.String,System.StringComparison)" or
            "System.Runtime:M:System.String.Equals(System.String,System.String,System.StringComparison)" or
            "System.Runtime:M:System.String.IndexOf(System.Char)" or
            "System.Runtime:M:System.String.IsNullOrEmpty(System.String)" or
            "System.Runtime:M:System.String.Join``1(System.Char,System.Collections.Generic.IEnumerable{``0})" or
            "System.Runtime:M:System.String.Replace(System.String,System.String,System.StringComparison)" or
            "System.Runtime:M:System.String.Split(System.Char,System.StringSplitOptions)" or
            "System.Runtime:M:System.String.StartsWith(System.String,System.StringComparison)" or
            "System.Runtime:M:System.String.Substring(System.Int32,System.Int32)" or
            "System.Runtime:M:System.String.ToLowerInvariant" or
            "System.Runtime:M:System.String.TrimStart(System.Char)" or
            "System.Runtime:M:System.String.TrimStart(System.Char[])" or
            "System.Runtime:M:System.Text.Encoding.GetBytes(System.String)" or
            "System.Runtime:M:System.Text.Encoding.GetString(System.ReadOnlySpan{System.Byte})" or
            "System.Runtime:M:System.Text.StringBuilder.#ctor" or
            "System.Runtime:M:System.Text.StringBuilder.Append(System.Char)" or
            "System.Runtime:M:System.Text.StringBuilder.Append(System.String)" or
            "System.Runtime:M:System.Text.StringBuilder.ToString" or
            "System.Runtime:M:System.ValueType.#ctor" or
            "System.Runtime:P:System.Array.Length" or
            "System.Runtime:P:System.Collections.Generic.IEnumerator`1.Current" or
            "System.Runtime:P:System.Collections.Generic.IReadOnlyCollection`1.Count" or
            "System.Runtime:P:System.Collections.Generic.IReadOnlyDictionary`2.Item(`0)" or
            "System.Runtime:P:System.Collections.Generic.IReadOnlyDictionary`2.Keys" or
            "System.Runtime:P:System.Collections.Generic.KeyValuePair`2.Key" or
            "System.Runtime:P:System.Collections.Generic.KeyValuePair`2.Value" or
            "System.Runtime:P:System.Collections.IEnumerator.Current" or
            "System.Runtime:P:System.Exception.Message" or
            "System.Runtime:P:System.Globalization.CultureInfo.InvariantCulture" or
            "System.Runtime:P:System.ReadOnlySpan`1.Empty" or
            "System.Runtime:P:System.ReadOnlySpan`1.Enumerator.Current" or
            "System.Runtime:P:System.ReadOnlySpan`1.Length" or
            "System.Runtime:P:System.String.Chars(System.Int32)" or
            "System.Runtime:P:System.String.Length" or
            "System.Runtime:P:System.StringComparer.Ordinal" or
            "System.Runtime:P:System.Text.Encoding.UTF8" or
            "System.Security.Cryptography:M:System.Security.Cryptography.SHA256.HashData(System.ReadOnlySpan{System.Byte},System.Span{System.Byte})" or
            "System.Text.Encoding.Extensions:M:System.Text.UTF8Encoding.#ctor(System.Boolean,System.Boolean)" or
            "System.Text.Encodings.Web:P:System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.Array" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.False" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.Null" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.Number" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.Object" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.String" or
            "System.Text.Json:F:System.Text.Json.JsonValueKind.True" or
            "System.Text.Json:M:System.Text.Json.JsonDocument.Parse(System.String,System.Text.Json.JsonDocumentOptions)" or
            "System.Text.Json:M:System.Text.Json.JsonElement.ArrayEnumerator.GetEnumerator" or
            "System.Text.Json:M:System.Text.Json.JsonElement.ArrayEnumerator.MoveNext" or
            "System.Text.Json:M:System.Text.Json.JsonElement.EnumerateArray" or
            "System.Text.Json:M:System.Text.Json.JsonElement.EnumerateObject" or
            "System.Text.Json:M:System.Text.Json.JsonElement.GetRawText" or
            "System.Text.Json:M:System.Text.Json.JsonElement.GetString" or
            "System.Text.Json:M:System.Text.Json.JsonElement.ObjectEnumerator.GetEnumerator" or
            "System.Text.Json:M:System.Text.Json.JsonElement.ObjectEnumerator.MoveNext" or
            "System.Text.Json:M:System.Text.Json.JsonElement.TryGetDecimal(System.Decimal@)" or
            "System.Text.Json:M:System.Text.Json.JsonElement.TryGetInt32(System.Int32@)" or
            "System.Text.Json:M:System.Text.Json.JsonElement.TryGetInt64(System.Int64@)" or
            "System.Text.Json:M:System.Text.Json.JsonElement.TryGetProperty(System.String,System.Text.Json.JsonElement@)" or
            "System.Text.Json:M:System.Text.Json.JsonSerializer.SerializeToElement``1(``0,System.Text.Json.JsonSerializerOptions)" or
            "System.Text.Json:M:System.Text.Json.JsonSerializer.SerializeToNode``1(``0,System.Text.Json.JsonSerializerOptions)" or
            "System.Text.Json:M:System.Text.Json.JsonSerializer.Serialize``1(``0,System.Text.Json.JsonSerializerOptions)" or
            "System.Text.Json:M:System.Text.Json.JsonSerializerOptions.#ctor" or
            "System.Text.Json:M:System.Text.Json.Nodes.JsonNode.AsObject" or
            "System.Text.Json:M:System.Text.Json.Nodes.JsonNode.Parse(System.String,System.Nullable{System.Text.Json.Nodes.JsonNodeOptions},System.Text.Json.JsonDocumentOptions)" or
            "System.Text.Json:P:System.Text.Json.JsonDocument.RootElement" or
            "System.Text.Json:P:System.Text.Json.JsonElement.ArrayEnumerator.Current" or
            "System.Text.Json:P:System.Text.Json.JsonElement.ObjectEnumerator.Current" or
            "System.Text.Json:P:System.Text.Json.JsonElement.ValueKind" or
            "System.Text.Json:P:System.Text.Json.JsonProperty.Name" or
            "System.Text.Json:P:System.Text.Json.JsonProperty.Value" or
            "System.Text.Json:P:System.Text.Json.JsonSerializerOptions.Encoder" or
            "System.Text.Json:P:System.Text.Json.Nodes.JsonNode.Item(System.String)" or
            "xunit.assert:M:Xunit.Assert.All``1(System.Collections.Generic.IEnumerable{``0},System.Action{``0})" or
            "xunit.assert:M:Xunit.Assert.Contains(System.String,System.String,System.StringComparison)" or
            "xunit.assert:M:Xunit.Assert.DoesNotContain``1(``0,System.Collections.Generic.IEnumerable{``0})" or
            "xunit.assert:M:Xunit.Assert.Empty(System.Collections.IEnumerable)" or
            "xunit.assert:M:Xunit.Assert.EndsWith(System.String,System.String,System.StringComparison)" or
            "xunit.assert:M:Xunit.Assert.Equal(System.String,System.String)" or
            "xunit.assert:M:Xunit.Assert.Equal``1(System.Collections.Generic.IEnumerable{``0},System.Collections.Generic.IEnumerable{``0})" or
            "xunit.assert:M:Xunit.Assert.Equal``1(``0,``0)" or
            "xunit.assert:M:Xunit.Assert.False(System.Boolean)" or
            "xunit.assert:M:Xunit.Assert.NotEqual``1(``0,``0)" or
            "xunit.assert:M:Xunit.Assert.NotNull(System.Object)" or
            "xunit.assert:M:Xunit.Assert.Null(System.Object)" or
            "xunit.assert:M:Xunit.Assert.Single``1(System.Collections.Generic.IEnumerable{``0})" or
            "xunit.assert:M:Xunit.Assert.Throws``1(System.Action)" or
            "xunit.assert:M:Xunit.Assert.Throws``1(System.Func{System.Object})" or
            "xunit.assert:M:Xunit.Assert.True(System.Boolean)" => true,
            _ => false,
        };
    }
}
