using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class EuclideanThreeLatticeTransferenceDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed nonzero integral-dual vector controls every covering error in dimensions three and four.",
        H("Euclidean lattice transference in dimensions three and four"),
        Blocks(Describe.Lean(
            DescribeId.Create("euclidean-three-lattice-transference"),
            DeclarationHandle.Create(Gid + ".exists_dual_covering"),
            H("Squared covering error times squared dual length is at most eleven twelfths"),
            StatementSource.FromAuthor(Disp(Statement(3, new Formula.Fraction(D(1, 1), D(1, 2))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The dual submodule is taken with respect to the real inner product on "
                    + "EuclideanSpace ℝ (Fin 3). The membership condition says that the inner "
                    + "product with every element of L is integral. The proof chooses y once "
                    + "for L, before the target x is given.")),
                Paragraph(Text(
                    "Project successively off shortest nonzero vectors a and b in the first "
                    + "two lattices. A shortest generator c of the last image yields the "
                    + "integral-dual vector y = c/‖c‖². Rounding along the last direction costs "
                    + "at most ‖c‖²/4 in squared distance. A reduced planar circumradius estimate "
                    + "bounds the squared perpendicular correction by ‖b‖²/2. Projection "
                    + "separation gives ‖c‖² ≥ 3‖b‖²/4, so the total squared error is at most "
                    + "(11/12)‖c‖². The squared dual length is 1/‖c‖².")),
                Paragraph(Text(
                    "The formal proof uses shortest-vector projection. The independent "
                    + "geometry-of-numbers derivation in Pro receipt "
                    + "e5e86a56-5405-4540-a08f-501fa628496f supplies the reduced planar "
                    + "circumradius argument and the resulting three-dimensional constant."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("euclidean-four-lattice-transference"),
            DeclarationHandle.Create(Gid + ".exists_dual_covering_four"),
            H("Squared covering error times squared dual length is at most 43/36"),
            StatementSource.FromAuthor(Disp(Statement(4, new Formula.Fraction(D(4, 3), D(3, 6))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take successive shortest nonzero vectors a, b, c and d, projecting "
                    + "orthogonally off each of a, b and c in turn. Write A₁, A₂, A₃ and A₄ "
                    + "for their squared lengths. The final projected lattice is generated "
                    + "over the integers by d. The vector y = d/A₄ pairs integrally with L "
                    + "under the real inner product, has squared length 1/A₄ and is fixed "
                    + "before the target x is chosen.")),
                Paragraph(Text(
                    "The two reduced planes use a and a centered lift of b in L, and c "
                    + "and a centered lift of d in the twice-projected lattice. Cover the "
                    + "projected target in the last plane first and lift its lattice correction "
                    + "to L. Then correct the residual in the first plane. Orthogonality "
                    + "lets the two squared covering bounds add.")),
                Paragraph(Text(
                    "The three successive squared lengths A₂, A₃ and A₄ satisfy "
                    + "A₂ ≤ 3A₄/2. In the lattice after the first projection, compare "
                    + "fractional lifts of c and of a centered lift of d, their translates "
                    + "by −b, and the difference of the fractional lifts. If A₄ < 2A₂/3, "
                    + "the absolute shear r of the centered lift lies in (1/3, 1/2]. "
                    + "The shortestness inequalities force both fractional coefficients "
                    + "into (s, 1 − s) for s = 5/6 − r. Their difference then gives a "
                    + "nonzero lattice vector shorter than b.")),
                Paragraph(Text(
                    "When the absolute shear in the last plane is at most 1/6, one has "
                    + "A₃ ≤ 36A₄/35. Combining 3A₂/4 ≤ A₃ with squared planar radius "
                    + "bounds A₂/2 and A₄/2 gives a total at most 83A₄/70. For shear "
                    + "at least 1/6, the last squared radius is at most 4A₄/9. The "
                    + "three-length estimate bounds the first squared radius by 3A₄/4, "
                    + "giving a total of at most 43A₄/36.")),
                Paragraph(Text(
                    "GPT Pro receipt 8e67eabf-9f4a-410b-9fb2-097cb4e85466 supplied the "
                    + "combined two-plane argument and the bound 67/54. An independent "
                    + "Codex derivation of the three-length estimate and exact polynomial "
                    + "verification sharpened the bound to 43/36."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula NormSquared(Formula value) => new Formula.Power(new Formula.Norm(value), D(2));

    private static Formula Statement(byte dimension, Formula bound)
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("EuclideanSpace", reals, Call("Fin", D(dimension)));
        Formula lattice = F.Id("L"), dualVector = F.Id("y"), target = F.Id("x"), point = F.Id("v");
        Formula inner = new Formula.Apply(
            new Formula.Subscript(Seq(Operatorname, Grp(F.Id("inner"))), F.Id("l")), [space]);
        Formula dual = Call("dualSubmodule", inner, lattice);
        Formula error = new Formula.Binary(target, FormulaBinaryOperator.Subtract, point);
        Formula product = new Formula.Binary(
            NormSquared(error), FormulaBinaryOperator.Multiply, NormSquared(dualVector));

        return Seq(
            Forall, Sp, lattice, Colon, Sp, Call("Submodule", new Formula.Integers(), space), Comma, Sp,
            OpenBracket, Call("DiscreteTopology", lattice), CloseBracket, Sp,
            OpenBracket, Call("IsZLattice", reals, lattice), CloseBracket, Comma, Sp,
            Exists, Sp, dualVector, Sp, InMacro, Sp, dual, Comma, Sp,
            dualVector, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Open, Forall, Sp, target, Colon, Sp, space, Comma, Sp,
            Exists, Sp, point, Sp, InMacro, Sp, lattice, Comma, Sp,
            product, Sp, Le, Sp, bound, Close);
    }
}
