using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class DefectTwoSourceBlindnessDocument : IScribeDocumentDefinition
{
    private static Formula SourceTotal(Formula tree) =>
        Call("total", Call("sourceTree", F.Id("g"), F.Id("h"), tree));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite binary tree built from two defect directions has zero cubic carry response.",
        H("Two-source determinant blindness"),
        Blocks(
            Paragraph(Text("Let E be F2 cubed, with the explicit sign table f0 of "
                + "(FC.4), its alternating correction b_m, and the character "
                + "ell_m(g)_i=f_m(g,u_i). Fix two coarse defect labels g and h. "
                + "A coefficient tree has a pair (a,b) in F2 squared at each leaf. "
                + "The source tree replaces "
                + "that leaf by ag+bh and retains each binary fork; total adds all "
                + "source labels. Let T denote the finite coefficient trees.")),
            Describe.Lean(
                DescribeId.Create("two-source-carry-blindness"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind"),
                H("No finite two-source tree detects the cubic carry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("g"), Comma, Sp,
                    F.Id("h"), InMacro, Sp, F.Id("E"), Comma, Sp,
                    F.Id("L"), Comma, Sp, F.Id("M"), Comma, Sp,
                    F.Id("R"), InMacro, Sp, F.Id("T"), Comma, Esc,
                    Call("dot", Call("carry", Call("ell", F.Id("m")),
                        SourceTotal(F.Id("L")), SourceTotal(F.Id("M"))),
                        SourceTotal(F.Id("R"))), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on each tree shows that its total "
                    + "remains in the plane spanned by g and h. Direct evaluation of "
                    + "the eight finite sign choices shows that their carry is the "
                    + "same wedge product. Pairing the carry of two tree totals "
                    + "with a third total from that plane is therefore zero. This "
                    + "claim concerns additive label composition, not a physical "
                    + "fusion operation or a nonzero OPE coefficient."))),
                DescribeRole.Theorem))));
}
