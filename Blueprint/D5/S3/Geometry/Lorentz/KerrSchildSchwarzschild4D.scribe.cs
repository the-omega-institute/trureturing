using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class KerrSchildSchwarzschild4DDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef WeylCopy => LibraryNoteRef.Create("D5/L/LieTheory/luna2019weyldoublecopy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Schwarzschild and Coulomb fields in the radial screen frame.",
        H("Schwarzschild and Coulomb Weyl double copy"),
        Blocks(
            Paragraph(Text("At the unit-radius point on the positive third spatial axis, use the jet j of "
                + "φ = p / |x| and k = (1, x / |x|). The frame T changes the Cartesian basis by the null "
                + "rank-one term −p k♯ ⊗ k / 2. Write B for the pair matrix of the full Riemann curvature "
                + "in T and C for the Ricci-free tensor with electric block diag(p/2, p/2, −p) and "
                + "zero magnetic block. Max is the Cartesian divergence of the Coulomb field with both indices raised. The bivector order is 01, 02, 03, 23, 31, 12.")),
            Describe.Lean(DescribeId.Create("schwarzschild-coulomb-copy"),
                DeclarationHandle.Create("D5/S3/Geometry/Lorentz/KerrSchildSchwarzschild4D.schwarzschild_coulomb_weyl_double_copy"),
                H("The normalized Weyl square at unit radius"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(WeylCopy),
                Blocks(Paragraph(Text("The field strength of A = φ k has only F₀₃ = p and F₃₀ = −p. "
                    + "Its contraction with the screen vector and the null generator is the projective "
                    + "evaluation of the Maxwell quadratic 2pX in degree two. The orthonormal curvature "
                    + "has spatial pair block opposite to its electric block. The harmonic scalar gives the zero time component of the Maxwell divergence through the stationary Poisson identity. The spatial components vanish by the radial derivative equations. The Weyl contraction is "
                    + "−12pX², so the scalar multiplying the Maxwell square is −3/p in these conventions."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement()
    {
        Formula p = F.Id("p");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula r = F.Id("r");
        Formula t = Call("T", p);
        Formula rays = Op("Ray");
        Formula pair = Op("PairIndex");
        Formula zero = D(0);
        Formula amplitude = Mul(D(2), p);
        Formula w = Call("W", Call("C", p));
        Formula q = Call("q", amplitude, zero, Infty);
        Formula square = Call("Q", amplitude, zero, Infty);
        Formula scalar = Seq(Frac, Grp(Seq(Minus, Sp, D(3))), Grp(p));
        Formula frame = Equal(Mul(Seq(Parens(t), Caret, Grp(F.Id("T"))), Call("g", p), t), Op("eta"));
        Formula matrix = All("i", pair, All("j", pair,
            Equal(Call("C", p, i, j), Call("B", p, Call("index", i), Call("index", j)))));
        Formula maxwell = All("r", rays, Equal(Call("CoulombScreen", p, r), Call("ev", D(2), r, q)));
        Formula vacuum = All("i", Call("Fin", D(4)), Equal(Call("Max", p, i), zero));
        return All("p", Seq(Mathbb, Grp(F.Id("R"))), Parens(Seq(NotEqual(p, zero), Sp, Implies, Sp,
            Parens(Seq(frame, Sp, Land, Sp, Parens(matrix), Sp, Land, Sp, Parens(maxwell), Sp, Land, Sp, Parens(vacuum), Sp, Land, Sp,
                Equal(w, Mul(scalar, square)))))));
    }

    private static Formula All(string name, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), ty, body);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Parens(Formula x) => Seq(Open, x, Close);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Mul(Formula x, Formula y, Formula z) => Mul(Mul(x, y), z);
}
