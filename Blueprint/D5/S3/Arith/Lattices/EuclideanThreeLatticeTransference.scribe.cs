using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class EuclideanThreeLatticeTransferenceDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed nonzero integral-dual vector controls every covering error in dimension three.",
        H("Euclidean three-dimensional lattice transference"),
        Blocks(Describe.Lean(
            DescribeId.Create("euclidean-three-lattice-transference"),
            DeclarationHandle.Create(Gid + ".exists_dual_covering"),
            H("Squared covering error times squared dual length is at most eleven twelfths"),
            StatementSource.FromAuthor(Disp(Statement())),
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
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula NormSquared(Formula value) => new Formula.Power(new Formula.Norm(value), D(2));

    private static Formula Statement()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("EuclideanSpace", reals, Call("Fin", D(3)));
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
            product, Sp, Le, Sp, new Formula.Fraction(D(1, 1), D(1, 2)), Close);
    }
}
