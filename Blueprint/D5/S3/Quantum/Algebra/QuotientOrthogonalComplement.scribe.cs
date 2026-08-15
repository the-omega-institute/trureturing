using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class QuotientOrthogonalComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical quotient isometrically identifies the orthogonal complement.",
        H("Quotient and Orthogonal Complement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-canonical-quotient-map-is-an-isometric-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/QuotientOrthogonalComplement."
                    + "quotient_orthogonal_complement_isometry"),
                H("The canonical quotient map is an isometric equivalence"),
                StatementSource.FromAuthor(QuotientOrthogonalComplementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a real-or-complex scalar field, E an inner-product space over k, "
                            + "and K a subspace admitting an orthogonal projection. The exact "
                            + "Mathlib map quotientEquivOrthogonal carries linearity in its type. "
                            + "The first two conjuncts state that its underlying function is an "
                            + "isometry and a bijection, hence a linear isometric equivalence from "
                            + "E modulo K onto the orthogonal complement of K.")),
                    Paragraph(Text(
                        "For every x in E, the last conjunct identifies the underlying vector of "
                            + "the image of the quotient class of x with x minus its canonical "
                            + "orthogonal projection onto K. Thus the formal statement includes "
                            + "both the source formula for the canonical map and the assertion "
                            + "that this map is an isometric equivalence.")),
                    Paragraph(Text(
                        "Loogle found Submodule.quotientEquivOrthogonal exactly. LeanSearch "
                            + "returned related quotient-complement equivalences but not that "
                            + "exact declaration among its first ten results. The pinned Mathlib "
                            + "tree contains the exact construction, which is imported and reused; "
                            + "its coercion theorem and the complementary-projection identity prove "
                            + "the displayed formula without reconstructing the equivalence."))),
                DescribeRole.Theorem))));

    private static Formula QuotientOrthogonalComplementFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula subspace = F.Id("K");
        Formula x = F.Id("x");
        Formula canonical = Call("quotientEquivOrthogonal", subspace);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("InnerProductSpace")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            subspace, Colon, Sp, Operatorname, Grp(F.Id("Submodule")), Underscore,
            Grp(scalar), Open, space, Close, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("HasOrthogonalProjection")),
            Open, subspace, Close, CloseBracket, Comma, Esc,
            Operatorname, Grp(F.Id("Isometry")), Open, canonical, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("Bijective")), Open, canonical, Close, Sp, Land, Sp,
            Open, Forall, Sp, x, Colon, Sp, space, Comma, Esc,
            canonical, Open, OpenBracket, x, CloseBracket, Close, Sp, Eq, Sp,
            x, Sp, Minus, Sp, Call("starProjection", subspace, x), Close, Dot));
    }
}
