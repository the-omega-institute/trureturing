using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PrefixFreeCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix-free and suffix-free codes decode uniquely, and finite binary prefix codes satisfy Kraft's inequality.",
        H("Prefix-Free Codes"),
        Blocks(
            Paragraph(Text(
                "A code is prefix-free when a codeword can prefix another codeword only if "
                + "they are equal. Dually, it is suffix-free when the same condition holds "
                + "for suffixes. The empty word is excluded from nondegenerate decoding.")),
            Describe.Lean(
                DescribeId.Create("prefix-free-nil-degeneracy"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_eq_singleton_nil"),
                H("The empty word makes a prefix-free code degenerate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsPrefixFree")), Open, F.Id("S"), Close,
                    Sp, Land, Sp, OpenBracket, CloseBracket, Sp, InMacro, Sp, F.Id("S"),
                    Sp, Rightarrow, Sp, F.Id("S"), Sp, Eq, Sp,
                    OpenBrace, OpenBracket, CloseBracket, CloseBrace, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty word prefixes every list. Prefix freedom therefore forces every "
                    + "member of a code containing it to equal the empty word, so the code is "
                    + "exactly the singleton containing that word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-free-first-codeword"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_first_codeword"),
                H("A prefix-free concatenation determines its first codeword"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("u"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    F.Id("v"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    F.Id("u"), Sp, Cdot, Sp, F.Id("x"), Sp, Eq, Sp,
                    F.Id("v"), Sp, Cdot, Sp, F.Id("y"), Sp, Rightarrow, Sp,
                    F.Id("u"), Sp, Eq, Sp, F.Id("v"), Sp, Land, Sp,
                    F.Id("x"), Sp, Eq, Sp, F.Id("y"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two leading codewords in equal concatenations are comparable by the prefix "
                    + "relation. Prefix freedom identifies them, and left cancellation then "
                    + "identifies the remaining tails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-free-uniquely-decodable"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isPrefixFree"),
                H("Prefix-free codes are uniquely decodable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsPrefixFree")), Open, F.Id("S"), Close,
                    Sp, Land, Sp, Neg, Sp, Open,
                    OpenBracket, CloseBracket, Sp, InMacro, Sp, F.Id("S"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("UniquelyDecodable")), Open, F.Id("S"), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on a list of codewords repeatedly applies first-codeword "
                    + "extraction. The empty-word side condition rules out a nonempty encoding "
                    + "whose flattened message is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-image-prefix-free"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.isSuffixFree_isPrefixFree_reverse_image"),
                H("Reversal sends suffix-free codes to prefix-free codes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsSuffixFree")), Open, F.Id("S"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("IsPrefixFree")), Open,
                    Operatorname, Grp(F.Id("reverse"), Sp, F.Id("image")),
                    Open, F.Id("S"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "List reversal turns a prefix relation between reversed codewords into a "
                    + "suffix relation between the originals. Suffix freedom then identifies "
                    + "the originals, and reversing again identifies their images."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("suffix-free-uniquely-decodable"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isSuffixFree"),
                H("Suffix-free codes are uniquely decodable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsSuffixFree")), Open, F.Id("S"), Close,
                    Sp, Land, Sp, Neg, Sp, Open,
                    OpenBracket, CloseBracket, Sp, InMacro, Sp, F.Id("S"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("UniquelyDecodable")), Open, F.Id("S"), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reverse every codeword and reverse the codeword order. Flattening this "
                    + "transformed list reverses the flattened message, so prefix-free unique "
                    + "decodability transports back through the involution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-free-binary-kraft-inequality"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.kraft_inequality_of_isPrefixFree"),
                H("Finite binary prefix codes satisfy Kraft's inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsPrefixFree")), Open, F.Id("S"), Close,
                    Sp, Land, Sp, Neg, Sp, Open,
                    OpenBracket, CloseBracket, Sp, InMacro, Sp, F.Id("S"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("kraft"), Sp, F.Id("sum")),
                    Open, F.Id("S"), Close, Sp, Leq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prefix-free bridge supplies the unique-decodability hypothesis to the "
                    + "repository's finite_binary_kraft_inequality theorem. The counting "
                    + "argument therefore remains visible through the existing import edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unique-decodability-strictly-weaker-than-prefix-freedom"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixFreeCode.exists_uniquelyDecodable_not_isPrefixFree"),
                H("Unique decodability is strictly weaker than prefix freedom"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("S"), Comma, Sp,
                    Operatorname, Grp(F.Id("UniquelyDecodable")), Open, F.Id("S"), Close,
                    Sp, Land, Sp, Neg, Sp,
                    Operatorname, Grp(F.Id("IsPrefixFree")), Open, F.Id("S"), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The binary code `{[0], [0,1]}` is suffix-free and hence uniquely "
                        + "decodable, while `[0]` is a proper prefix of `[0,1]`. This explicit "
                        + "witness proves that the bridge has no converse.")),
                    Paragraph(Text(
                        "Pinned mathlib and the repository were searched before proving. They "
                        + "provide unique decodability, Kraft-McMillan, and the list reversal "
                        + "lemmas used here, but no existing prefix-code predicate or theorem. "
                        + "The converse Kraft construction, infinite codes, and the halting-set "
                        + "application remain outside this deposit."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/KraftInequality"))]));
}
