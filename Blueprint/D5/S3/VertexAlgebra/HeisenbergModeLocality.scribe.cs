using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class HeisenbergModeLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Heisenberg mode relation gives second-order locality and identifies the exact first-order obstruction.",
        H("Heisenberg Mode Locality"),
        Blocks(
            Paragraph(Text(
                "Let V be a rational vector space and A a Mathlib VertexOperator on V. "
                + "Its normalized mode A_m is VertexOperator.ncoeff A m, the coefficient "
                + "of z raised to -m-1. Put C_A(m,n) = A_m composed with A_n minus A_n "
                + "composed with A_m. For any two-index endomorphism function F, put "
                + "Delta F(m,n) = F(m+1,n) - F(m,n+1). This is multiplication by z-w "
                + "on coefficients with the normalized exponents.")),
            Describe.Lean(
                DescribeId.Create("heisenberg-modes-are-local-of-order-two"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/HeisenbergModeLocality.heisenberg_mode_locality"),
                H("Heisenberg modes are local of order two"),
                StatementSource.FromAuthor(LocalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "CCR(A,K) means that, for every pair of integer indices m,n, "
                        + "C_A(m,n) equals m times K when m+n is zero and is zero otherwise. "
                        + "Here K is any rational-linear endomorphism. Under this relation, "
                        + "the second coefficient shift of C_A vanishes at every pair, the "
                        + "first shift at (0,-1) is K, and the first shift vanishes everywhere "
                        + "if and only if K is zero.")),
                    Paragraph(Text(
                        "The first shift is K exactly on the antidiagonal m+n+1=0. "
                        + "Its next shift therefore subtracts equal values, while the "
                        + "coefficient (0,-1) detects K. The statement assumes the mode "
                        + "relation and supplies neither a Fock representation nor the "
                        + "vacuum, translation, or Jacobi axioms of a vertex algebra."))),
                DescribeRole.Theorem))));

    private static Formula Modes(byte order, Formula m, Formula n) => Seq(
        order == 1 ? Seq(Delta, Sp) : Seq(Delta, Caret, Grp(D(order)), Sp),
        F.Id("C"), Underscore, Grp(F.Id("A")), Open, m, Comma, n, Close);

    private static Formula AllModes(Formula body) => Seq(
        Forall, Sp, F.Id("m"), Comma, F.Id("n"), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, body);

    private static Formula LocalityFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var k = F.Id("K");
        return Disp(Seq(
            Call("CCR", F.Id("A"), k), Sp, Rightarrow, Sp,
            Open, AllModes(Seq(Modes(2, m, n), Sp, Eq, Sp, D(0))), Close,
            Sp, Land, Sp,
            Open, Modes(1, D(0), Seq(Minus, D(1))), Sp, Eq, Sp, k, Close,
            Sp, Land, Sp,
            Open, Open, AllModes(Seq(Modes(1, m, n), Sp, Eq, Sp, D(0))), Close,
            Sp, Iff, Sp, k, Sp, Eq, Sp, D(0), Close));
    }
}
