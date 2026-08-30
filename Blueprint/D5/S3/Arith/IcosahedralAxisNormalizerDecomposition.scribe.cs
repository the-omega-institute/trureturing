using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class IcosahedralAxisNormalizerDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/IcosahedralAxisNormalizerDecomposition."
            + "finite_icosahedral_axis_decomposition_with_normalizers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three finite projective axis classes explicitly biject with the complete "
            + "6/10/15 cyclic-axis decomposition and have normalizer orders 10/6/4.",
        H("Icosahedral Axis Normalizer Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-icosahedral-axis-decomposition-with-normalizers"),
            DeclarationHandle.Create(Declaration),
            H("The finite axis decomposition has the stated normalizers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The projective classes and cyclic-axis families are the canonical objects "
                    + "from the finite axis decomposition. The statement publishes their "
                    + "partition together with three structural maps to the unique cyclic axes "
                    + "that fix the corresponding projective directions. Their bijectivity, "
                    + "cardinalities, normalizer orders, and the twofold normalizer-centralizer "
                    + "identification are published in the same statement."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula projectiveFive = ProjectiveClass(D(5));
        Formula projectiveThree = ProjectiveClass(D(3));
        Formula projectiveTwo = ProjectiveClass(D(2));
        Formula cyclicFive = CyclicClass(D(5));
        Formula cyclicThree = CyclicClass(D(3));
        Formula cyclicTwo = CyclicClass(D(2));

        return Disp(new Formula.Aligned([
            Seq(
                UnionOf(UnionOf(projectiveFive, projectiveThree), projectiveTwo),
                Sp, Eq, Sp, Call("univ", F.Id("FiniteProjectivePlane")), Sp, Land, Sp,
                Call("Disjoint", projectiveFive, projectiveThree), Sp, Land, Sp,
                Call("Disjoint", projectiveFive, projectiveTwo), Sp, Land, Sp,
                Call("Disjoint", projectiveThree, projectiveTwo), Sp, Land),
            Seq(BijectionClause(
                    "fivefoldProjectiveAxisMap", projectiveFive, cyclicFive),
                Sp, Land, Sp,
                BijectionClause(
                    "threefoldProjectiveAxisMap", projectiveThree, cyclicThree),
                Sp, Land, Sp,
                BijectionClause(
                    "twofoldProjectiveAxisMap", projectiveTwo, cyclicTwo),
                Sp, Land),
            Seq(FixedAxisClause(
                    "fivefoldProjectiveAxisMap", projectiveFive),
                Sp, Land, Sp,
                FixedAxisClause(
                    "threefoldProjectiveAxisMap", projectiveThree),
                Sp, Land, Sp,
                FixedAxisClause(
                    "twofoldProjectiveAxisMap", projectiveTwo),
                Sp, Land),
            Seq(
                Card(projectiveFive), Sp, Eq, Sp, D(6), Sp, Land, Sp,
                Card(projectiveThree), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
                Card(projectiveTwo), Sp, Eq, Sp, D(1, 5), Sp, Land),
            Seq(
                Card(projectiveFive), Sp, Eq, Sp, Card(cyclicFive), Sp, Land, Sp,
                Card(projectiveThree), Sp, Eq, Sp, Card(cyclicThree), Sp, Land, Sp,
                Card(projectiveTwo), Sp, Eq, Sp, Card(cyclicTwo), Sp, Land),
            Seq(
                Card(cyclicFive), Sp, Eq, Sp, D(6), Sp, Land, Sp,
                Card(cyclicThree), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
                Card(cyclicTwo), Sp, Eq, Sp, D(1, 5), Sp, Land),
            Seq(ConjugacyClause(D(5)), Sp, Land),
            Seq(ConjugacyClause(D(3)), Sp, Land),
            Seq(ConjugacyClause(D(2)), Sp, Land),
            Seq(NormalizerCardClause(D(5), D(1, 0)), Sp, Land),
            Seq(NormalizerCardClause(D(3), D(6)), Sp, Land),
            Seq(NormalizerCardClause(D(2), D(4)), Sp, Land),
            Seq(TwofoldCentralizerClause(), Dot),
        ]));
    }

    private static Formula BijectionClause(
        string map, Formula source, Formula target) => Seq(
            Operatorname, Grp(F.Id("Bijective")), Open,
            F.Id(map), Colon, Sp, source, Sp, To, Sp, target, Close);

    private static Formula FixedAxisClause(string map, Formula source)
    {
        Formula point = F.Id("p");
        return Seq(
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            Call("axisFixesProjectivePoint", Call(map, point), point));
    }

    private static Formula NormalizerCardClause(Formula order, Formula cardinality)
    {
        Formula axis = F.Id("g");
        return Seq(
            Forall, Sp, axis, Colon, Sp, CyclicClass(order), Comma, Sp,
            Card(Call("cyclicAxisNormalizer", order, axis)),
            Sp, Eq, Sp, cardinality);
    }

    private static Formula ConjugacyClause(Formula order)
    {
        Formula left = F.Id("g");
        Formula right = F.Id("h");
        return Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, CyclicClass(order), Comma, Sp,
            Call("axesAreConjugate", order, left, right));
    }

    private static Formula TwofoldCentralizerClause()
    {
        Formula axis = F.Id("g");
        return Seq(
            Forall, Sp, axis, Colon, Sp, CyclicClass(D(2)), Comma, Sp,
            Call("cyclicAxisNormalizer", D(2), axis), Sp, Eq, Sp,
            Call("elementCentralizer", axis));
    }

    private static Formula Card(Formula carrier) => Seq(
        Operatorname, Grp(F.Id("card")), Open, carrier, Close);

    private static Formula ProjectiveClass(Formula order) =>
        new Formula.Subscript(F.Id("P"), order);

    private static Formula CyclicClass(Formula order) =>
        new Formula.Subscript(F.Id("A"), order);

    private static Formula UnionOf(Formula left, Formula right) => Seq(
        Operatorname, Grp(F.Id("union")), Open, left, Comma, Sp, right, Close);
}
