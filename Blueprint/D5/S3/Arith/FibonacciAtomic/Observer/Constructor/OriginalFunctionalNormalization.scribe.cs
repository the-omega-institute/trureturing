using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalFunctionalNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFunctionalNormalization", H("Functional native expressions and root links"), Blocks(
            Describe.Lean(DescribeId.Create("native-fixed-powers"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_power"),
                H("Distribution of every fixed native power"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Expressions retain finite grounds, named parameter atoms, a literal Omega, decorated state variables and ordered pairs. A parameter name has its fixed finite or divergent mode. Literal Omega is available even when there are no parameters. The power operation distributes the actual native substitution over pairs, composes variable decorations, shifts finite atoms and evaluates finite grounds. It introduces no independent unary tree constructor."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-substitution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_subst"),
                H("Simultaneous substitution preserves evaluation"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A reconstruction is one expression for each original state name. Simultaneous substitution evaluates that expression with the same valuation at every occurrence. Parameter names and their coincidences are retained; ordered pairs may evaluate to atomic values. FunctionalCase also retains the arithmetic guard and a finite family of expressions for every designated original residual."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-link-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.root_link_normalization"),
                H("Exact elimination of all defining root links"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A functional system has at most one defining expression for each state; undefined states remain unrestricted. The normalized system has no decorated variable as a defining root. Its remaining state occurrences are strictly below a pair. Every normalized solution reconstructs an original solution. Conversely, an original solution satisfies the normalized equations and is fixed by reconstruction. Substituting the same reconstruction into every designated residual preserves all original coordinates.")),
                    Paragraph(Text("Eliminating a nonself link substitutes its decorated target everywhere and retains its reconstruction. A zero self-link imposes no condition and becomes free. A positive self-link forces the actual leafless Omega: iteration of its positive period and native eventual full prefixes exclude every leaf. Each elimination strictly decreases the finite set of root-link definitions. Thus normalization needs no supplied graph rank, finite expansion bound, solvability premise or fixed point.")),
                    Paragraph(Text("The system and reconstruction depend on syntax alone, independently of natural parameter values. Both semantic directions hold for all finite state and parameter counts, including zero, with unrestricted completed free values. The arithmetic guard is retained as a condition on the original parameter tuple; it is never replaced by existence of a solution. This is a native semantic normalization result, with no external novelty claim."))
                ), DescribeRole.Theorem)
        )));
}
