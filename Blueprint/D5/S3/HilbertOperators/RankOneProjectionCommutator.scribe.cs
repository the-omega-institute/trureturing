using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class RankOneProjectionCommutatorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/HilbertOperators/RankOneProjectionCommutator.norm_rankOne_projection_commutator";

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(V(name)), Open, Seq(args), Close);
    private static Formula TypeAt(string level) =>
        Seq(Operatorname, Grp(V("Type")), Underscore, Grp(V(level)));
    private static Formula R => new Formula.Subscript(V("R"), V("v"));
    private static Formula Pv => Seq(V("P"), V("v"));
    private static Formula Complement => Seq(V("v"), Minus, Pv);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact operator norm of a rank-one commutator with an orthogonal projection.",
        H("Rank-one commutator with an orthogonal projection"),
        Blocks(Describe.Lean(DescribeId.Create("rank-one-projection-commutator-norm"),
            DeclarationHandle.Create(Declaration),
            H("Exact commutator norm"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Amp, Forall, Sp, V("i"), Colon, Call("UniverseLevel"), Comma,
                    V("j"), Colon, Call("UniverseLevel"), Comma),
                Seq(Amp, Forall, Sp, V("K"), Colon, TypeAt("i"), Comma,
                    V("H"), Colon, TypeAt("j"), Comma),
                Seq(Amp, OpenBracket, Call("RCLike", V("K")), CloseBracket,
                    OpenBracket, Call("SeminormedAddCommGroup", V("H")), CloseBracket,
                    OpenBracket, Call("InnerProductSpace", V("K"), Comma, V("H")), CloseBracket, Comma),
                Seq(Amp, Forall, Sp, V("P"), Colon, Call("ContinuousLinearMap", V("K"), Comma, V("H"), Comma, V("H")),
                    Comma, Call("IsSymmetricProjection", V("P")), Rightarrow, Sp,
                    Forall, Sp, V("v"), Colon, V("H"), Comma),
                Seq(Amp, new Formula.Norm(Seq(R, Sp, Circ, Sp, V("P"), Minus, V("P"), Sp, Circ, Sp, R)),
                    Eq, new Formula.Norm(Pv), new Formula.Norm(Complement))
            ]))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The scalar field K is real or complex in the sense of RCLike. "
                    + "The space H carries the seminorm induced by its inner product. "
                    + "The condition IsSymmetricProjection means that P is idempotent and "
                    + "symmetric for the inner product. The operator R indexed by v sends x "
                    + "to the inner product of v with x times v. The left side uses the operator norm.")),
                Paragraph(Text("Write a for Pv and b for v minus Pv. The two vectors are orthogonal "
                    + "and their squared norms add to the squared norm of v. Symmetry of P moves P "
                    + "from the input of the first rank-one map to the inner product's first slot. "
                    + "The commutator on x is the inner product of a with x times b minus the inner "
                    + "product of b with x times a.")),
                Paragraph(Text("These two output terms are orthogonal even after scalar multiplication. "
                    + "In the first inner product only Px contributes. In the second only x minus Px "
                    + "contributes. Applying Cauchy–Schwarz in the two terms bounds the squared norm of "
                    + "the output by the product of the squared norms of a and b times the sum of "
                    + "the squared norms of Px and x minus Px. The latter sum equals the squared norm "
                    + "of x by orthogonality.")),
                Paragraph(Text("The commutator sends a to its squared norm times b. When the seminorm "
                    + "of a is positive, testing the operator bound on a gives the reverse inequality, "
                    + "including when b has zero seminorm. When a has zero seminorm, the upper bound "
                    + "already gives equality.")),
                Paragraph(Text("Idempotence rules out twice the identity, which commutes with "
                    + "every rank-one operator and gives a positive product for a vector of positive "
                    + "seminorm. Symmetry rules out oblique projections. For example, the real "
                    + "plane map sending (x, y) to (x + y, 0) fixes (1, 0) but does not commute "
                    + "with the rank-one map for (1, 0).")),
                Paragraph(Text("In the directed Behrend shell, the three lost-vertex outcomes have "
                    + "orthonormal local difference vectors. The unit sign vector has squared overlap "
                    + "one third with each of them. For a subset of m outcomes, take P to be their "
                    + "sum of projections and v to be the sign vector. The two squared norms on the "
                    + "right are m divided by three and (three minus m) divided by three.")),
                Paragraph(Text("On the lost subspace, a unitary with phase z on the sign line and "
                    + "phase w on the standard component is w times the identity plus z minus w "
                    + "times the sign projection. Its commutator with a coarse outcome projection "
                    + "therefore has norm equal to the modulus of z minus w times the square root "
                    + "of m times (three minus m), divided by three. Multiplication by the adjoint "
                    + "unitary converts the commutator to the conjugation difference up to sign. "
                    + "The same norm gives the supremum of the absolute probability change over "
                    + "unit input vectors because the conjugation difference is self-adjoint. Adding "
                    + "the surviving-subspace outcome to the coarse subset gives the same norm "
                    + "when the unitary preserves that subspace."))),
            DescribeRole.Theorem))));
}
