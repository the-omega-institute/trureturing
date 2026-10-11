using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class NativeUnificationCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/NativeUnificationCore.";
    private static DocumentBlock Entry(string id, string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact native terms and finite presentations.", H("Exact native terms and finite presentations"), Blocks(
            Paragraph(Text("The finite-map primitives and original Strata monotype representation are licensed reuse from strata-org/Strata at a74043b69b98d4197dfd7d59df1b4427dcfc3f37. The native codec establishes the new exact inverse and constructor/support laws. The explicit presentation covers every original variable; it is not restricted to variables occurring in equations.")),
            Entry("schema-presentation", "Presentation", "Effective complete variable presentations", "A presentation enumerates every member of the original type X and supplies a computable String code and Option decoder. Decoding an encoded variable returns that variable, and every successful name decode re-encodes to the original identifier. Empty variable types are included.", DescribeRole.Definition),
            Entry("leaf", "leaf", "Two distinct nullary leaves", "False and true have distinct nullary constructor names. They represent the two generators of FreeMagma Bool.", DescribeRole.Definition),
            Entry("pair", "pair", "Ordered binary pairing", "The pair constructor has exactly two ordered children. Other names and other arities are outside the native fragment.", DescribeRole.Definition),
            Entry("encode", "encode", "Literal term encoding", "Term X is exactly FreeMagma (Bool sum X). Encoding preserves both Boolean leaves, every original variable and every binary branch.", DescribeRole.Definition),
            Entry("encodeground", "encodeGround", "Ground source encoding", "Ground sources are actual FreeMagma Bool trees, with their original Boolean labels and ordered binary branches.", DescribeRole.Definition),
            Entry("evaluate", "evaluate", "Native term evaluation", "The existing free-magma lift evaluates Boolean generators as leaves and variables by one supplied assignment.", DescribeRole.Definition),
            Entry("schema-shape", "Shape", "Exact constructor fragment", "Shape contains arbitrary variables, exactly two distinct nullary Boolean constructors, and exactly one binary pair constructor. It does not contain bit vectors, foreign names or malformed arities.", DescribeRole.Definition),
            Entry("nativedecode", "nativeDecode", "Checked structural decoding", "The total Option decoder checks the exact native constructor names and arities and the original-variable name decoder. It fails outside that domain.", DescribeRole.Definition),
            Entry("schema-supported", "Supported", "Original-variable support", "Every free identifier must be the code of an original variable; this support condition is separate from constructor shape.", DescribeRole.Definition),
            Entry("decode-encode", "decode_encode", "Left inverse", "For every presentation and every original native term t, decoding its encoding is some t.", DescribeRole.Theorem),
            Entry("encode-injective", "encode_injective", "Faithful native encoding", "The checked inverse makes the term encoding injective, including the distinct Boolean leaves and repeated variables.", DescribeRole.Theorem),
            Entry("encode-shape", "encode_shape", "Encoding preserves native constructors", "Every encoded term has the exact native constructor shape.", DescribeRole.Theorem),
            Entry("encode-supported", "encode_supported", "Encoding uses original variables", "Every free identifier of an encoded term is the code of an original member of X.", DescribeRole.Theorem),
            Entry("decode-exact", "decode_exact", "Decoding the complete fragment", "For every presentation p and type tree t with exact Shape and original-variable Supported, there is a native term whose successful decoding and re-encoding recover exactly t.", DescribeRole.Theorem),
            Entry("finname", "finName", "Computable ordinal identifiers", "The unary word of length n gives a computable finite-ordinal identifier.", DescribeRole.Definition),
            Entry("finpresentation", "finPresentation", "Effective ordinal presentation", "Fin n has an explicit complete enumeration, unary-word encoding and checked decoder for all n, including zero.", DescribeRole.Definition),
            Entry("transport", "transport", "Presentation transport", "A supplied equivalence transports the complete enumeration and both naming laws to the original type.", DescribeRole.Definition),
            Entry("finitepresentation", "finitePresentation", "All finite original variable types", "Every finite type X admits the full presentation data. Algorithm execution uses an explicitly supplied presentation, while the mathematical scope includes every finite X.", DescribeRole.Definition),
            Entry("encode-decode", "encode_decode", "Right inverse and rejection", "Every successful structural decode re-encodes to exactly the input type tree. Thus a bit vector, foreign constructor or malformed arity cannot decode into a native term.", DescribeRole.Theorem),
            Entry("decode-domain", "decode_domain", "Exact decoding domain", "For every p and t, existence of a successful decoded term is equivalent to exact native constructor shape together with original-variable support.", DescribeRole.Theorem))));
}
