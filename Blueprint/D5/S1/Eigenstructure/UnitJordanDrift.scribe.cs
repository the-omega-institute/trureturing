using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class UnitJordanDriftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unit Jordan block accumulates its fixed coordinate as exact linear drift.",
        H("Unit Jordan Drift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-jordan-iterate-eq-linear-drift"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/UnitJordanDrift."
                    + "unit_jordan_iterate_eq_linear_drift"),
                H("Unit Jordan iterates have exact linear drift"),
                StatementSource.FromAuthor(LinearDriftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J act on a pair by J(x,y)=(x+y,y). For every additive "
                        + "monoid and every natural n, its nth iterate fixes y and sends "
                        + "the first coordinate to x+n y. Thus the generalized coordinate "
                        + "contributes a secular term that is exactly linear in n.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no packaged unit-Jordan "
                        + "iterate formula. The proof reuses Function.iterate_succ_apply' and "
                        + "succ_nsmul, so only the one-step recursion is proved by induction.")),
                    Paragraph(Text(
                        "This closes only the source atom's statement that a nontrivial Jordan "
                        + "block at eigenvalue one produces secular drift. The logarithmic-clock "
                        + "decomposition, winding-number quantization, resonance interpretation, "
                        + "and every numerical certificate in appendix E.16 remain outside the theorem."))),
                DescribeRole.Theorem))));

    private static Formula LinearDriftFormula()
    {
        Formula carrier = F.Id("A");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula jordan = F.Id("J");
        Formula vector = Seq(Open, x, Comma, Sp, y, Close);
        Formula iterate = Seq(jordan, Caret, Grp(OpenBracket, n, CloseBracket), vector);
        Formula drifted = Seq(Open, x, Plus, n, Sp, Cdot, Sp, y, Comma, Sp, y, Close);

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, carrier, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, carrier, Comma, Esc,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            iterate, Sp, Eq, Sp, drifted, Dot));
    }
}
