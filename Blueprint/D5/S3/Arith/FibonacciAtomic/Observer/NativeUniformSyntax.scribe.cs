using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformSyntaxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformsyntax-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformSyntax", H("NativeUniformSyntax"), Blocks(
            Paragraph(Text("Original old-class names and frontier addresses determine the finite syntax. Repeated class occurrences share their reconstructed term, and the complete old-disequality list stays separate from the singleton equation sent to unification. The original native presentation is connected to finite ordinals through its actual variable-list enumeration.")),
            Entry("tree_of_prim", "Fixed preorder codes admit primitive recursive leaf construction. Leaf construction supplies the syntax and tree algorithms.", DescribeRole.Theorem),
            Entry("tree_mul_prim", "Fixed preorder codes admit primitive recursive binary construction. The construction joins serialized subtrees without changing order.", DescribeRole.Theorem),
            Entry("prefixKeys", "Prefix the original frontier address without changing its old class label.", DescribeRole.Definition),
            Entry("ordinalTerm", "Replace each original class-address key by its position in the cell variable table, retaining every Boolean constructor and repeated occurrence.", DescribeRole.Definition),
            Entry("oldCode", "Parse the class pattern word and reconstruct its original frontier keys. Missing class words and malformed pattern words return none.", DescribeRole.Definition),
            Entry("cellSyntax", "Use the sorted native class names, exact pattern-family words and the original variable-key list.", DescribeRole.Definition),
            Entry("cellTerm", "Translate a native cell term through its original keys and their ordinals.", DescribeRole.Definition),
            Entry("wholeCode", "Expand every occurrence of an old class with the same class term. Boolean leaves and the ordered tree structure remain explicit.", DescribeRole.Definition),
            Entry("whole_code_prim", "The structural expansion of a finite literal row is primitive recursive in its finite pattern and variable tables.", DescribeRole.Theorem),
            Entry("whole_code_exact", "Reconstruction through the original class table produces exactly the ordinal translation of the native whole term, preserving repeated class occurrences.", DescribeRole.Theorem),
            Entry("namePairs", "List every pair of distinct old numeric classes once, in native class order with the smaller name first.", DescribeRole.Definition),
            Entry("traverseCodes", "Traverse a finite list in order, returning none if any component is malformed. The finite cursor proof uses computable natural-number recursion and permits computable callbacks.", DescribeRole.Definition),
            Entry("traverse_computable", "A finite traversal of computable partial callbacks is computable and preserves list order. The explicit cursor and natural recursion allow a merely computable native solver.", DescribeRole.Theorem),
            Entry("traverse_map_exact", "An exact component correspondence transports through ordered traversal. This correspondence relates generated finite words to native pattern families and pair plans.", DescribeRole.Theorem),
            Entry("deltaCode", "Reconstruct the complete ordered old-disequality list from class pattern words. These pairs are checked after unifying a singleton new equality; they are never supplied as extra equalities.", DescribeRole.Definition),
            Entry("delta_code_exact", "The generated old inequalities coincide with the entire native ordered disequality list after variable translation.", DescribeRole.Theorem),
            Entry("delta_code_computable", "Computably reconstruct every ordered old-disequality pair using the same class terms used by the whole row.", DescribeRole.Theorem),
            Entry("syntax_legal_code_exact", "The full ordinal disequality test is equivalent to native syntax legality, using injectivity of original class-address coordinates. No old disequality is dropped or passed to the unifier as an equality.", DescribeRole.Theorem),
            Entry("nativePairCode", "Serialize the native plan with original cell ordinals, both addresses, the exact branch and ordered ground template words.", DescribeRole.Definition),
            Entry("native_pair_exact", "For every original native pattern cell, the computable singleton-equation plan equals the exact original presentation plan, including the fully composed action and actual bound-variable domain.", DescribeRole.Theorem),
            Entry("cell_term_rename", "The syntax reconstruction agrees with renaming each original variable by its unique position in the native variable list. This equality connects syntax to presentation transport.", DescribeRole.Theorem))));
}
