using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdCoverComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.";
    private static readonly LibraryNoteRef TwistedCurrents =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full third-cover Virasoro representation splits into the ordinary central-charge-one action and a concrete complementary central-charge-two action.",
        H("The Complementary Grids of the Third Cover"),
        Blocks(
            Paragraph(Text("Retain the two native residue grids with indices indivisible by three. The full rank-one covering "
                + "action is ThirdCoverVirasoro.coverMode, of central charge three, and its scalar shift at zero is 1/9. "
                + "ThirdCoverIntegerFactor identifies the divisible-by-three summands with the ordinary charge-one "
                + "action. The remaining polynomial factor is constructed explicitly below by pointwise finite normal "
                + "ordering.")),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-complement-mode"),
                DeclarationHandle.Create(Prefix + "complementMode"),
                H("Native complementary oscillator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive native index k+1 not divisible by three acts as (k+1) times partial differentiation in its "
                           + "complementary variable. The negative mode -(k+1) acts by multiplication by that variable. Divisible "
                           + "indices and zero act by zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-mode-join-complement"),
                DeclarationHandle.Create(Prefix + "mode_join_complement"),
                H("A complementary native mode acts on the second factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any nonzero scaling of the ordinary variables, a native mode with index indivisible by three acts "
                           + "on join(P tensor Q) as join(P tensor complementMode(r)(Q)). The derivative of the ordinary renamed "
                           + "polynomial in that variable vanishes, and the creation case uses the complementary generator formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-split-complement-mode"),
                DeclarationHandle.Create(Prefix + "split_complementMode"),
                H("Complementary modes on all split states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("By tensor extensionality, conjugating an indivisible native mode by split gives the identity tensor "
                           + "complementMode(r)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-complement-pair"),
                DeclarationHandle.Create(Prefix + "complementPair"),
                H("Normal order on the complementary factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compose the two complementary native modes with the smaller index on the left. The larger index acts "
                           + "first, as in the native normalPair definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-fractional-virasoro"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro"),
                H("Fractional Virasoro operators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each integer m, use one third of one half of the normal-ordered sum with pairs (3m-k,k) over k "
                           + "indivisible by three, and add 1/9 times the identity at m=0. The support bound is transported from the "
                           + "full native action through the ordinary vacuum slice. Additivity and complex linearity follow from "
                           + "pointwise finite support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-cover-sub-integer-join-tmul"),
                DeclarationHandle.Create(Prefix + "cover_sub_integer_join_tmul"),
                H("Complement of the integral Sugawara sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero s, subtract integerSugawara(m) from the merged coverMode(m) acting on join(P tensor "
                           + "Q). The finite sum separates into the complementary and integral index sets, and both indices 3m-k and "
                           + "k are complementary together. Transport the remaining pairs through join to obtain join(P tensor "
                           + "fractionalVirasoro(m)(Q))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-split-cover-sub-integer"),
                DeclarationHandle.Create(Prefix + "split_cover_sub_integer"),
                H("Complement operator on all split states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pure-tensor subtraction implies that conjugation sends the cover minus its integral summand to "
                           + "identity tensor fractionalVirasoro(m)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-split-cover-mode"),
                DeclarationHandle.Create(Prefix + "split_coverMode"),
                H("Factorization of the full cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex s with s squared equal to three, conjugation by split sends coverMode(m) to L(m) "
                           + "tensor identity plus identity tensor fractionalVirasoro(m). This follows by adding the ordinary "
                           + "Sugawara intertwiner to the complementary subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-fractional-virasoro-commutator"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_commutator"),
                H("Virasoro law at central charge two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all integers n and m, the commutator equals (n-m) fractionalVirasoro(n+m) plus 2(n^3-n)/12 times "
                           + "the identity when n+m=0. Under split the two factor actions commute. Conjugate the merged cover "
                           + "commutator at charge three, subtract the native L commutator at charge one, and cancel the injective "
                           + "tensor extension. Injectivity follows by evaluating on 1 tensor Q and applying join."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-fractional-virasoro-vacuum"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_vacuum"),
                H("Highest-weight vacuum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonnegative integer m, fractionalVirasoro(m)(1) is 1/9 times 1 if m=0 and zero otherwise. In "
                           + "each pair with sum 3m, the larger index is nonnegative and therefore annihilates the constant "
                           + "polynomial before the other mode acts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-fractional-current"),
                DeclarationHandle.Create(Prefix + "fractionalCurrent"),
                H("Normalized complementary current"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply complementMode(r) by the inverse of the chosen square root of three. The frequency r/3 lies "
                           + "in the complementary grids when r is indivisible by three."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thirdcovercomplement-fractional-current-commutator"),
                DeclarationHandle.Create(Prefix + "fractionalCurrent_commutator"),
                H("Heisenberg bracket on the complementary factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCurrents),
                Blocks(Paragraph(Text("When r and t are indivisible by three, the commutator equals r/3 times the identity if r+t=0 and zero "
                           + "otherwise. Conjugate the first component of ThirdCoverVirasoro.current_commutator and use the "
                           + "second-factor current intertwiner and tensor injectivity. Bakalov and Kac, arXiv:math/0402315v1, "
                           + "equation (4.23), gives the fractional Heisenberg bracket convention. The concrete factor proof here is "
                           + "a repository derivation."))),
                DescribeRole.Theorem),
            Paragraph(Text("This establishes a concrete polynomial oscillator factor and its operator relations. The "
                + "identification with a full lattice twisted-module state-field action and the sixteen-pair assembly "
                + "require additional constructions.")))));
}
