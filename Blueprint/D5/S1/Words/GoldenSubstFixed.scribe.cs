using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenSubstFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locate consecutive Fibonacci-substitution blocks and identify each block "
            + "pointwise with the infinite golden word.",
        H("Pointwise Substitution Fixed Point of the Golden Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("substitution-block-start"),
                DeclarationHandle.Create("D5/S1/Words/GoldenSubstFixed.goldenSubstStart"),
                H("True-count partial sums locate substitution block starts"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The image of each true letter has length two, while the image of each "
                                    + "false letter has length one. The block for source index i therefore "
                                    + "starts at i plus the number of true letters strictly before i."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("consecutive-substitution-block-boundaries"),
                DeclarationHandle.Create("D5/S1/Words/GoldenSubstFixed.goldenSubstStart_succ"),
                H("Consecutive substitution blocks meet at their boundaries"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                                    Operatorname, Grp(F.Id("goldenSubstStart")),
                                    Open, F.Id("i"), Plus, D(1), Close, Eq,
                                    Operatorname, Grp(F.Id("goldenSubstStart")), Open, F.Id("i"), Close,
                                    Plus, Operatorname, Grp(F.Id("length")), Open,
                                    Operatorname, Grp(F.Id("subst")), Open,
                                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close,
                                    Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Advancing one source index adds exactly the length of that letter's "
                                    + "substitution image. Thus the computed boundaries are consecutive, with "
                                    + "neither gaps nor overlaps between adjacent image blocks."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("golden-word-is-pointwise-substitution-fixed"),
                DeclarationHandle.Create("D5/S1/Words/GoldenSubstFixed.golden_word_substitution_fixed"),
                H("Every substituted source block agrees pointwise with the golden word"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                                    Forall, Sp, F.Id("j"), InMacro,
                                    Operatorname, Grp(F.Id("Fin")), Open,
                                    Operatorname, Grp(F.Id("length")), Open,
                                    Operatorname, Grp(F.Id("subst")), Open,
                                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close,
                                    Close, Close, Close, Comma, Esc,
                                    Operatorname, Grp(F.Id("goldenWord")), Open,
                                    Operatorname, Grp(F.Id("goldenSubstStart")),
                                    Open, F.Id("i"), Close, Plus, F.Id("j"), Close, Eq,
                                    Operatorname, Grp(F.Id("get")), Open,
                                    Operatorname, Grp(F.Id("subst")), Open,
                                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close,
                                    Close, Comma, F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For every source index i and every valid offset j in its substitution "
                                    + "image, the infinite golden word at the computed block position equals "
                                    + "the j-th image letter. The proof identifies the corresponding block in "
                                    + "a finite Fibonacci-word substitution and then passes to the diagonal "
                                    + "golden-word limit; it requires no global output-to-source inverse."))),
                DescribeRole.Theorem
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenWord")),
        ]));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
