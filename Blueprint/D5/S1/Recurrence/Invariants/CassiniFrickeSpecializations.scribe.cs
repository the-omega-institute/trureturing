using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CassiniFrickeSpecializationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generic Cassini-Fricke identity specializes to signed log coordinates "
        + "and a conserved absolute value.",
        H("Cassini-Fricke Log-Coordinate Specializations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cassini-fricke-log-coordinate-identity"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations."
                    + "cassini_fricke_log_coordinate_identity"),
                H("The log-coordinate quadratic value alternates in sign"),
                StatementSource.FromAuthor(SignedIdentity()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first chain clause introduces u_K and Q but ends before its displayed "
                        + "conclusion. This declaration makes those definitions explicit in its "
                        + "expanded quadratic expression and supplies the signed identity needed "
                        + "to complete that chain stem.")),
                    Paragraph(Text(
                        "It directly applies the repository theorem cassini_fricke to Mathlib's "
                        + "goldenRatio and goldenConj with A = -x*phi and B = y*psi. Their product "
                        + "is -1, which turns A*B into x*y, so no recurrence identity is "
                        + "reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cassini-fricke-absolute-conservation"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations."
                    + "cassini_fricke_absolute_conservation"),
                H("The absolute quadratic value is conserved"),
                StatementSource.FromAuthor(AbsoluteConservation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Taking absolute values of the signed specialization removes the factor "
                        + "(-1)^(K+1) and yields 5*|x*y|. Thus consecutive signed values differ by "
                        + "a sign, while their magnitude is independent of K.")),
                    Paragraph(Text(
                        "The zero-axis and diagonal readings in the source follow by substituting "
                        + "y = 0 and x = y into this formula. The theorem records the common "
                        + "conservation law rather than duplicating those immediate leaf cases."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Recurrence/CassiniFricke")),
        ]));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula U(Formula index) => Subscript(F.Id("u"), index);

    private static Formula J(Formula index) => Subscript(F.Id("J"), index);

    private static Formula Q(Formula left, Formula right) =>
        Seq(F.Id("Q"), Open, left, Comma, Sp, right, Close);

    private static Formula SignedIdentity()
    {
        Formula k = F.Id("K");
        Formula kPlusOne = Seq(k, Plus, D(1));

        return Disp(Seq(
            U(k), Sp, Colon, Eq, Sp,
            Minus, F.Id("x"), Phi, Caret, Grp(kPlusOne), Sp, Plus, Sp,
            F.Id("y"), Psi, Caret, Grp(kPlusOne), Comma, Esc,
            F.Id("Q"), Open, F.Id("a"), Comma, Sp, F.Id("b"), Close,
            Sp, Colon, Eq, Sp,
            F.Id("a"), Caret, Grp(D(2)), Sp, Minus, Sp,
            F.Id("a"), F.Id("b"), Sp, Minus, Sp,
            F.Id("b"), Caret, Grp(D(2)), Comma, Esc,
            J(k), Sp, Colon, Eq, Sp, Q(U(kPlusOne), U(k)), Sp, Eq, Sp,
            D(5), Sp, Cdot, Sp, F.Id("x"), Sp, Cdot, Sp,
            F.Id("y"), Sp, Cdot, Sp,
            Open, Minus, D(1), Close, Caret, Grp(kPlusOne)));
    }

    private static Formula AbsoluteConservation()
    {
        Formula k = F.Id("K");
        return Disp(Seq(
            Lvert, Sp, J(k), Rvert, Sp, Eq, Sp,
            D(5), Sp, Cdot, Sp, Lvert,
            Sp, F.Id("x"), Sp, Cdot, Sp, F.Id("y"), Rvert));
    }
}
