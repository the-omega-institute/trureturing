using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private LeanSourceDeclaration CustomSyntaxSource(
        LeanSourceDeclaration context, LeanSourceDeclaration extractionOwner) => context with
    {
        FullName = "<custom-syntax:" + context.FullName + ">",
        Kind = "custom-syntax-source-closure", IsProof = false,
        SemanticTokens = [], AmbientTokens = [],
        ManagedSourceClosure = ReachableManagedSources(extractionOwner),
    };

    private bool UsesCustomSyntax(LeanSourceDeclaration declaration)
    {
        if (IsGeneratorClosure(declaration))
        {
            if (declarations.Where(source => source.Path == declaration.Path).Any(UsesCustomSyntax)) return true;
            foreach (var command in GeneratorCommands(declaration.AmbientTokens))
            {
                var isRules = command.Any(static token => token.Text is "macro_rules" or "elab_rules");
                if (UsesCustomSyntaxTokens(declaration, isRules ? command
                    : command.SkipWhile(static token => token.Text != "=>").Skip(1))) return true;
            }
            return false;
        }

        return UsesCustomSyntaxTokens(declaration, declaration.SemanticTokens)
            || ImplicitInstanceCommands(declaration.AmbientTokens)
                .Any(command => UsesCustomSyntaxTokens(declaration, command));
    }

    private bool UsesCustomSyntaxTokens(
        LeanSourceDeclaration declaration, IEnumerable<LeanSourceToken> tokens)
    {
        var semantic = tokens
            .Select(static token => LeanCustomSyntaxCatalog.NormalizeLiteral(token.Text))
            .ToImmutableHashSet(StringComparer.Ordinal);
        return customSyntaxCatalog.VisibleFrom(declaration).Any(semantic.Contains);
    }
}
