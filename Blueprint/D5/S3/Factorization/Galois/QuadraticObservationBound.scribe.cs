using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class QuadraticObservationBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/QuadraticObservationBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary group observers see no more than the square quotient.",
        H("Quadratic Observation Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-subgroup-le-quadratic-joint-kernel"),
                DeclarationHandle.Create(
                    Prefix + "square_subgroup_le_quadratic_joint_kernel"),
                H("Every binary observer kills the square subgroup"),
                StatementSource.FromAuthor(UpperFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A quadratic observer is any group homomorphism to the "
                            + "multiplicative form of ZMod 2; surjectivity is not assumed.")),
                    Paragraph(Text(
                        "The named squareSubgroup is the normal closure of all squares. "
                            + "Every observer sends each square to one, so this subgroup "
                            + "lies in the intersection of all observer kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "square-quotient-exponent-divides-two-and-commutative"),
                DeclarationHandle.Create(
                    Prefix + "square_quotient_exponent_divides_two_and_commutative"),
                H("The square quotient is an elementary abelian two-quotient"),
                StatementSource.FromAuthor(QuotientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every element of the quotient squares to one. Mathlib's exponent "
                        + "interface gives exponent dividing two, and its order-two "
                        + "commutation lemma makes the quotient commutative. No finiteness "
                        + "or commutativity hypothesis on the original group is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-readout-has-collision"),
                DeclarationHandle.Create(Prefix + "quadratic_readout_has_collision"),
                H("A nontrivial square subgroup forces a joint-readout collision"),
                StatementSource.FromAuthor(CollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a nonidentity element of the square subgroup. The upper-bound "
                        + "theorem puts it in every observer kernel, so it and the identity "
                        + "have the same complete binary readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nontrivial-square-subgroup-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "nontrivial_square_subgroup_is_necessary"),
                H("The strictness hypothesis is necessary on C2"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For C2 every square is one, while the identity observer belongs to "
                        + "the full observer family and separates both elements. This is "
                        + "the concrete counterexample obtained by deleting the nontrivial "
                        + "square-subgroup hypothesis."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("zmod-four-strictness-example"),
                DeclarationHandle.Create(Prefix + "zmod_four_strictness_example"),
                H("C4 is a named cyclic two-group strict example"),
                StatementSource.FromAuthor(ZModFourFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The multiplicative form of ZMod 4 is commutative, and the square "
                            + "of one is the nonidentity element two. Hence its square "
                            + "subgroup is nontrivial and the joint readout has a collision.")),
                    Paragraph(Text(
                        "The remaining Lean audits cover an empty carrier, the trivial "
                            + "group, the constant observer, and a noncommutative S3 example. "
                            + "There is no finite-cardinality assumption or numeric depth."))),
                DescribeRole.Lemma))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Cyclic(Formula order) =>
        Seq(F.Id("C"), Underscore, Grp(order));

    private static Formula Square(Formula group) =>
        Seq(group, Caret, Grp(D(2)));

    private static Formula UpperFormula()
    {
        Formula group = F.Id("G");
        return Disp(Seq(
            Square(group), Sp, Leq, Sp, Call(F.Id("JointKernel"), group), Dot));
    }

    private static Formula QuotientFormula()
    {
        Formula group = F.Id("G");
        Formula quotient = Call(F.Id("Quotient"), group, Square(group));
        return Disp(Seq(
            Call(F.Id("exponent"), quotient), Sp, Mid, Sp, D(2), Sp, Land, Sp,
            Call(F.Id("Commutative"), quotient), Dot));
    }

    private static Formula CollisionFormula()
    {
        Formula group = F.Id("G");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Square(group), Sp, Neq, Sp, OpenBrace, D(1), CloseBrace, Sp,
            Rightarrow, RowBreak, Grp(), Exists, Sp, x, Comma, Sp, y, InMacro, Sp,
            group, Comma, Sp, x, Sp, Neq, Sp, y, Sp, Land, Sp,
            Call(F.Id("Readout"), x), Sp, Eq, Sp, Call(F.Id("Readout"), y), Dot));
    }

    private static Formula NecessityFormula()
    {
        Formula cTwo = Cyclic(D(2));
        return Disp(Seq(
            Square(cTwo), Sp, Eq, Sp, OpenBrace, D(1), CloseBrace, Sp, Land, Sp,
            Call(F.Id("Injective"), Call(F.Id("Readout"), cTwo)), Dot));
    }

    private static Formula ZModFourFormula()
    {
        Formula cFour = Cyclic(D(4));
        return Disp(Seq(
            Call(F.Id("Commutative"), cFour), Sp, Land, Sp,
            Square(cFour), Sp, Neq, Sp, OpenBrace, D(1), CloseBrace, Sp, Land, Sp,
            Neg, Call(F.Id("Injective"), Call(F.Id("Readout"), cFour)), Dot));
    }
}
