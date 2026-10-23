using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal static class ScribeLeanInputs
{
    internal static ImmutableArray<string> Select(string root, IEnumerable<string> paths)
    {
        var selection = ScribeDefinitionSelector.Select(root, paths);
        if (!selection.IsSuccess) throw new InvalidOperationException(selection.Failure);
        if (selection.Paths.IsEmpty)
            throw new InvalidOperationException("Scribe Lean input scope is empty.");
        var admission = ScribeSdkAdmission.Check(root, selection.Paths);
        if (admission.ExitCode != 0)
        {
            var error = new StringWriter();
            admission.WriteFailure(error);
            throw new InvalidOperationException(error.ToString().Trim());
        }

        var results = ScribeScriptHost.ExecuteBatch(root, selection.Paths);
        var failures = results.Where(static result => !result.IsSuccess).ToArray();
        if (failures.Length != 0)
            throw new InvalidOperationException(string.Join("\n", failures.Select(static result => result.Failure)));

        return results.SelectMany(static result =>
        {
            var document = result.Definition!.Document;
            return DocumentGraphAssembler.Extract(document)
                .OfType<DocumentEdge.TruthAnchor>()
                .Select(static anchor => anchor.Target.Reference.Path.Value[..^5].Replace('/', '.'))
                .Append(document.Header.Gid.Value.Replace('/', '.'));
        }).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
    }
}
