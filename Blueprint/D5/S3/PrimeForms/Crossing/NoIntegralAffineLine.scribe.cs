using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class NoIntegralAffineLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The crossing quadratic surface contains no nonconstant integral affine line.",
        H("No Integral Affine Line on the Crossing Surface"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crossing-surface-has-no-nonconstant-integral-affine-line"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/NoIntegralAffineLine."
                    + "crossing_surface_has_no_nonconstant_integral_affine_line"),
                H("Every integral affine line on the surface is constant"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp,
                    F.Id("b"), Comma, F.Id("c"), Comma, F.Id("t"), Comma,
                    F.Id("u"), Comma, F.Id("v"), Comma, F.Id("w"),
                    InMacro, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    Open, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    Open, F.Id("b"), Plus, F.Id("n"), F.Id("u"), Close,
                    Caret, Grp(D(2)), Minus,
                    Open, F.Id("b"), Plus, F.Id("n"), F.Id("u"), Close,
                    Open, F.Id("c"), Plus, F.Id("n"), F.Id("v"), Close, Plus,
                    Open, F.Id("c"), Plus, F.Id("n"), F.Id("v"), Close,
                    Caret, Grp(D(2)), Minus,
                    Open, F.Id("t"), Plus, F.Id("n"), F.Id("w"), Close,
                    Caret, Grp(D(2)), Eq, Minus, D(1), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("u"), Eq, D(0), Sp, Land, Sp,
                    F.Id("v"), Eq, D(0), Sp, Land, Sp,
                    F.Id("w"), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose every integer point of the affine line with base point (b,c,t) "
                        + "and direction (u,v,w) lies on b^2 - bc + c^2 - t^2 = -1. "
                        + "Then its direction is zero, so the line is constant.")),
                    Paragraph(Text(
                        "Evaluating at n = 0, 1, and -1 separates the base-point equation, "
                        + "the direction's null-cone equation, and their bilinear orthogonality. "
                        + "The binary quadratic identity 4 q(b,c) q(u,v) - B^2 = "
                        + "3 (bv-cu)^2 then turns the surface value -1 into a sum-of-squares "
                        + "obstruction, forcing w, v, and u successively to vanish.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact theorem excluding "
                        + "integral affine lines from this indefinite quadratic surface. LeanSearch "
                        + "returned only generic affine-line and quadratic-map declarations, including "
                        + "AffineMap.lineMap_eq_lineMap_iff and QuadraticMap.PosDef.anisotropic, neither "
                        + "of which proves this case. The proof therefore uses Mathlib's ring and "
                        + "nlinarith tactics for the explicit polynomial and nonnegativity steps.")),
                    Paragraph(Text(
                        "This formalizes only appendix E.33's explicitly named no-integral-line lemma. "
                        + "It does not claim the surrounding half-dimension theorem or any counting "
                        + "estimate for the exceptional set."))),
                DescribeRole.Theorem
            )),
        []));
}
