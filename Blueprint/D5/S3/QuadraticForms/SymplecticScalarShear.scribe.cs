using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SymplecticScalarShearDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t, Formula body) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula And(params Formula[] xs) => Seq(xs.SelectMany((x, i) => i == 0 ? new[] { Grp(x) } : new[] { Sp, Land, Sp, Grp(x) }).ToArray());
    private static Formula Statement => Disp(Seq(
        All("n", Call("Nat")), All("P", Call("RealMatrix", Seq(D(2), V("n")), Seq(D(2), V("n")))),
        Imp(Call("SymplecticJ0", V("P"), V("n")),
            Ex("t", Call("Nat"),
                And(Seq(V("t"), Sp, Le, Sp, V("n")),
                    Ex("E", Call("RealMatrix", V("n")),
                        Ex("H", Call("RealMatrix", V("n")),
                            Ex("R", Call("RealMatrix", V("n")),
                                And(
                                    Seq(V("E"), Sp, Eq, Sp, Call("aPlusScalarMulB", V("P"), V("t"))),
                                    Call("IsUnitDet", V("E")),
                                    Seq(V("H"), Sp, Eq, Sp, Call("nonsingInvMul", V("E"), Call("bBlock", V("P")))),
                                    Seq(V("R"), Sp, Eq, Sp, Call("nonsingInvMulRight", Call("cPlusScalarMulD", V("P"), V("t")), V("E"))),
                                    Call("Symmetric", V("H")), Call("Symmetric", V("R")),
                                    Call("ScalarShearFactorization", V("P"), V("t"), V("E"), V("H"), V("R")))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite real J0-symplectic block matrix admits a bounded scalar shear making the upper-left block invertible and factors into symmetric shears, a dilation and the prescribed Fourier block.",
        H("Symplectic scalar-shear factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("symplectic-scalar-shear-factorization"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/SymplecticScalarShear.exists_scalar_shear_factorization"),
            H("Bounded scalar shear and exact factorization"),
            StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For P = [[a,b],[c,d]] with P J0 P^T = J0 and J0 = [[0,I],[-I,0]], the theorem chooses a natural t <= n such that E = a + t b has nonzero determinant. It defines H = E^-1 b and R = (c+t d) E^-1, proves both are symmetric, and returns the exact six-factor identity P = N_R G_E J0 N_-H J0^-1 N_-tI. No invertibility assumption is made on a or b; n = 0 is included.")),
                Paragraph(Text("The proof uses the symplectic block identities, positive definiteness of aa^T+bb^T, the complex determinant at i, and the degree bound for det(a+Xb). The real polynomial argument is a finite existence choice; it makes no computability claim for equality over arbitrary real inputs.")),
                Paragraph(Text("This is a reusable matrix prerequisite for later quantum-unitary work. It does not establish the Schwartz, L2, Weyl, Gibbs, entropy, tensor-product or parent R22 analytic statements."))),
            DescribeRole.Theorem))));
}
