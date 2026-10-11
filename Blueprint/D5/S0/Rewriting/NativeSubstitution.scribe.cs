using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class NativeSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/NativeSubstitution.";
    private static DocumentBlock Entry(string id, string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native substitution closure.", H("Native substitution closure"), Blocks(
            Paragraph(Text("The original scoped substitution, its well-formedness, key-exclusion and idempotence proofs are licensed Strata reuse. Native closure is proved for the exact Boolean-leaf and binary-pair grammar by induction under these operations, independently of variable support.")),
            Entry("schema-nativesubst", "NativeSubst", "Native substitution values", "Every stored substitution value has the exact native constructor shape; this concerns all stored values, independently of the key and free-variable bounds.", DescribeRole.Definition),
            Entry("shape-subst", "shape_subst", "Substitution closure", "Applying a substitution with native values to a native term preserves the native constructor shape.", DescribeRole.Theorem),
            Entry("native-insert", "native_insert", "Insertion closure", "Inserting one native value into a substitution with native values preserves that invariant.", DescribeRole.Theorem),
            Entry("native-apply", "native_apply", "Composition closure", "Mapping a native singleton substitution through all stored values preserves the native constructor shape.", DescribeRole.Theorem),
            Entry("shape-children", "shape_children", "Constructor decomposition", "Every argument of a native constructor tree is native. This supplies both sides of each decomposed equation.", DescribeRole.Theorem))));
}
