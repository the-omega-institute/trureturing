using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativeBirthVectorDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-level native birth vectors decode exactly the finite original prefix pattern.",
        H("Native Birth-Vector Decoder"),
        Blocks(
            Paragraph(Text("Address is the finite binary-word type and Source is the existing native source algebra. "
                + "Pattern d is the finite original-prefix pattern at depth d. LevelAddress d contains exactly the "
                + "addresses of length d, and a LevelVector d assigns a natural-number code to every such address. "
                + "birthVector collects the recursively defined birthAt code: the empty address has code zero, "
                + "an atomic source uses pathThreshold for alpha and its natural-number predecessor for beta, "
                + "and a pair selects the child named by the first address bit without an epoch shift. "
                + "patternVector is the corresponding code obtained from the decomposed original prefix.")),
            Paragraph(Text("The statements below concern these recursive codes. Interpreting birthAt as the least "
                + "epoch of actual presence over the full Source/address family requires a separate bridge to "
                + "native subtree navigation under iterated substitution; the decomposition and decoder "
                + "identities do not supply that bridge.")),
            Paragraph(Text("decodeBirth tests the rightmost address for the alpha and beta sentinel codes at "
                + "positive depth and otherwise recurses on the left and right blocks. Its proved guarantee is "
                + "decodeBirth d (patternVector d p) = some p for every depth d and pattern p. Acceptance does "
                + "not certify membership in the patternVector image: at depth zero every input returns some (), "
                + "including a vector with nonzero entry, although every depth-zero pattern vector is zero.")),
            Describe.Lean(DescribeId.Create("birth-vector-decomposition"),
                DeclarationHandle.Create(Prefix + "birthVector_decompose"), H("Native birth vectors are pattern vectors"),
                StatementSource.FromAuthor(Seq(Forall, Sp, V("d"), Sp, InMacro, Sp, V("Nat"), Comma, Sp,
                    Forall, Sp, V("u"), Sp, InMacro, Sp, V("Source"), Comma, Sp,
                    Call("birthVector", V("d"), V("u")), Sp, Eq, Sp,
                    Call("patternVector", V("d"),
                        Seq(Call("decompose", V("d"), V("u")), Dot, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The address recursion follows the root constructor. An atomic root uses "
                    + "the path threshold (or its predecessor for beta), while a pair root selects the child block "
                    + "matching the first address bit. Induction over depth therefore identifies the complete vector "
                    + "with the vector of the original prefix pattern."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decode-birth-pattern-vector"),
                DeclarationHandle.Create(Prefix + "decodeBirth_patternVector"), H("The decoder is exact on image vectors"),
                StatementSource.FromAuthor(Seq(Forall, Sp, V("d"), Sp, InMacro, Sp, V("Nat"), Comma, Sp,
                    Forall, Sp, V("p"), Sp, InMacro, Sp, Call("Pattern", V("d")), Comma, Sp,
                    Call("decodeBirth", V("d"), Call("patternVector", V("d"), V("p"))), Sp, Eq, Sp,
                    Call("some", V("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At depth zero the decoder returns the unique unit pattern. At positive depth, "
                    + "atomic alpha and beta roots are separated by the two rightmost sentinel values. For a pair "
                    + "root, the rightmost code is bounded below both sentinels, and the two block projections are "
                    + "the child pattern vectors. The induction hypothesis reconstructs both children and hence the "
                    + "pair pattern."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pattern-vector-bound"),
                DeclarationHandle.Create(Prefix + "patternVector_bound"), H("Pattern-vector codes are bounded by twice the depth"),
                StatementSource.FromAuthor(Seq(Forall, Sp, V("d"), Sp, InMacro, Sp, V("Nat"), Comma, Sp,
                    Forall, Sp, V("p"), Sp, InMacro, Sp, Call("Pattern", V("d")), Comma, Sp,
                    Forall, Sp, V("a"), Sp, InMacro, Sp, Call("LevelAddress", V("d")), Comma, Sp,
                    Call("patternVector", V("d"), V("p"), V("a")), Sp, Leq, Sp, Seq(D(2), Sp, Times, Sp, V("d")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The path-threshold bound is proved by induction on the address. Pair patterns "
                    + "inherit the bound from the selected child at one smaller depth; atomic patterns use the same "
                    + "threshold bound and the predecessor inequality."))), DescribeRole.Lemma))));
}
