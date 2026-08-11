using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class CodeFixedPointDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Kleene =
        LibraryNoteRef.Create("D5/L/Diagonal/kleene1938notation");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Every computable transformation of partial recursive codes fixes some code's behavior.",
            H("The Code Fixed-Point Theorem"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("computable-code-transformations-fix-a-behavior"),
                    DeclarationHandle.Create("D5/S0/Computability/CodeFixedPoint.code_fixed_point"),
                    H("Computable code transformations fix a behavior"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("F"), Colon, Operatorname, Grp(F.Id("Code")), To, Sp,
                        Operatorname, Grp(F.Id("Code")), Esc, F.Text,
                        Grp(F.Id("computable")), Rightarrow, Sp,
                        Exists, Sp, F.Id("e"), Comma, Sp,
                        Operatorname, Grp(F.Id("eval")), Open, F.Id("e"), Close,
                        Sp, Eq, Sp,
                        Operatorname, Grp(F.Id("eval")), Open, F.Id("F"), Open,
                        F.Id("e"), Close, Close, Dot))),
                    AssessedProvenance.FromLiterature(Kleene),
                    Blocks(
                        Paragraph(Text(
                            "For every computable total transformation of partial recursive "
                            + "codes there is a code whose described program behaves exactly "
                            + "as the program described by the transformed code. The "
                            + "transformation may rewrite programs arbitrarily - permute "
                            + "them, pad them, or replace them wholesale - yet as long as it "
                            + "is itself computable, it cannot change every behavior: some "
                            + "program is semantically indistinguishable from its own image. "
                            + "This is the recursion-theoretic fixed point that powers "
                            + "self-referential program constructions, and it is deposited "
                            + "here as the kernel form of the fixed-point principle for "
                            + "computable code transformations.")),
                        Paragraph(Text(
                            "The library was searched before proving: the pinned Mathlib "
                            + "already holds this statement as its fixed-point theorem on "
                            + "partial recursive codes, next to the second recursion theorem "
                            + "derived from it. The Lean declaration is therefore a declared "
                            + "thin honest wrapper: it applies the upstream theorem and "
                            + "restates the equality with the fixed code on the left. The "
                            + "classical construction behind the upstream proof is the "
                            + "diagonal self-application of a substitution code recorded in "
                            + "the attested note."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("consecutive-code-numerals-share-a-behavior"),
                    DeclarationHandle.Create("D5/S0/Computability/CodeFixedPoint.exists_consecutive_codes_equal_behavior"),
                    H("Consecutive code numerals share a behavior"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Exists, Sp, F.Id("e"), Comma, Sp,
                        Operatorname, Grp(F.Id("eval")), Open, F.Id("e"), Close,
                        Sp, Eq, Sp,
                        Operatorname, Grp(F.Id("eval")), Open,
                        Operatorname, Grp(F.Id("ofNat")), Open,
                        Operatorname, Grp(F.Id("encode")), Open, F.Id("e"), Close,
                        Plus, D(1), Close, Close, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The fixed point is instantiated at a concrete nontrivial "
                            + "transformation: decode a code to its numeral, add one, and "
                            + "re-encode. That successor transformation is computable, so "
                            + "some pair of consecutive code numerals describes one and the "
                            + "same partial function - the standard numbering of programs "
                            + "repeats a behavior at adjacent addresses. The instantiation "
                            + "keeps the wrapper honest: the wrapped theorem is quantified "
                            + "over all computable transformations, and this witness "
                            + "exercises it on one that moves every code. The application "
                            + "is classical folklore; its formal statement here is derived "
                            + "in the repository from the wrapped theorem, so it is "
                            + "conservatively recorded as repository-derived."))),
                    DescribeRole.Theorem))));
}
