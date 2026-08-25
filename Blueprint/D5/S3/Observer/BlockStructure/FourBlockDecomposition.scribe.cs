using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class FourBlockDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/BlockStructure/FourBlockDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An operator splits into four blocks with visible and residual domain-codomain types.",
        H("Four-Block Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("operator-is-the-sum-of-four-projection-blocks"),
                DeclarationHandle.Create(Prefix + "four_block_decomposition"),
                H("An operator is the sum of its four projection blocks"),
                StatementSource.FromAuthor(FourBlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In any possibly noncommutative ring, let Q equal one minus P. "
                            + "Inserting P plus Q on both sides of T expands T into PTP, "
                            + "PTQ, QTP, and QTQ.")),
                    Paragraph(Text(
                        "The identity needs neither idempotence nor a nontrivial carrier. "
                            + "It includes zero dynamics, identity dynamics, P equal to zero "
                            + "or one, and empty-index matrix rings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complement-relation-is-necessary"),
                DeclarationHandle.Create(Prefix + "complement_relation_is_necessary"),
                H("The complement relation cannot be omitted"),
                StatementSource.FromAuthor(ComplementCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Over the integers, take P and Q to be zero and T to be one. "
                            + "Then Q is not one minus P, and every proposed block is zero, "
                            + "so their sum is not T."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typed-blocks-realize-projection-products"),
                DeclarationHandle.Create(Prefix + "typed_block_formulas"),
                H("The four typed blocks realize the ambient projection products"),
                StatementSource.FromAuthor(TypedBlocksFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a subspace V admitting orthogonal projection, the four bundled "
                            + "continuous linear maps have types V to V, V-perp to V, V to "
                            + "V-perp, and V-perp to V-perp.")),
                    Paragraph(Text(
                        "After coercion into the ambient space, their values are exactly PTP, "
                            + "PTQ, QTP, and QTQ. The domain and codomain claims are therefore "
                            + "checked by Lean's types rather than recorded only in prose."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orthogonal-four-block-decomposition"),
                DeclarationHandle.Create(Prefix + "orthogonal_four_block_decomposition"),
                H("Orthogonal projection gives the typed four-block decomposition"),
                StatementSource.FromAuthor(OrthogonalDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The projections onto V and its orthogonal complement sum to the "
                            + "identity. Splitting both the input and each output of T gives "
                            + "the four ambient projection products.")),
                    Paragraph(Text(
                        "Only the HasOrthogonalProjection instance is assumed. Completeness "
                            + "of the ambient space and a separate closedness hypothesis are "
                            + "not needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commutator-is-the-off-diagonal-corollary"),
                DeclarationHandle.Create(Prefix + "commutator_off_diagonal_corollary"),
                H("The commutator is the off-diagonal corollary"),
                StatementSource.FromAuthor(CommutatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With Q equal to one minus P, the commutator of P and T is PTQ "
                            + "minus QTP. The Lean proof directly invokes the existing adjacent "
                            + "commutator theorem rather than constructing a second proof."))),
                DescribeRole.Lemma))));

    private static Formula Product(Formula left, Formula middle, Formula right) =>
        Multiply(Multiply(left, middle), right);

    private static Formula FourBlockSum(
        Formula projection,
        Formula complement,
        Formula map) =>
        Add(
            Add(
                Add(
                    Product(projection, map, projection),
                    Product(projection, map, complement)),
                Product(complement, map, projection)),
            Product(complement, map, complement));

    private static Formula Orthogonal(Formula space) =>
        Seq(space, Caret, Grp(Perp));

    private static Formula FourBlockFormula()
    {
        Formula algebra = F.Id("A");
        Formula projection = F.Id("P");
        Formula complement = F.Id("Q");
        Formula map = F.Id("T");

        return Disp(Seq(
            Forall, Sp, algebra, Comma, Sp,
            OpenBracket, Call("Ring", algebra), CloseBracket, Comma, Sp,
            Forall, Sp, projection, Comma, Sp, complement, Comma, Sp, map,
            Sp, InMacro, Sp, algebra, Comma, Sp,
            Equal(complement, Subtract(D(1), projection)), Sp, Rightarrow, Sp,
            Equal(map, FourBlockSum(projection, complement, map)), Dot));
    }

    private static Formula ComplementCounterexampleFormula()
    {
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula projection = F.Id("P");
        Formula complement = F.Id("Q");
        Formula map = F.Id("T");

        return Disp(Seq(
            projection, Sp, Eq, Sp, D(0), Comma, Sp,
            complement, Sp, Eq, Sp, D(0), Comma, Sp,
            map, Sp, Eq, Sp, D(1), Sp, InMacro, Sp, integers, Comma, Sp,
            complement, Sp, Neq, Sp, Subtract(D(1), projection), Sp, Land, Sp,
            map, Sp, Neq, Sp, FourBlockSum(projection, complement, map), Dot));
    }

    private static Formula TypedBlocksFormula()
    {
        Formula visible = F.Id("V");
        Formula residual = Orthogonal(visible);
        Formula ptp = F.Id("PTP");
        Formula ptq = F.Id("PTQ");
        Formula qtp = F.Id("QTP");
        Formula qtq = F.Id("QTQ");

        return Disp(Seq(
            ptp, Colon, Sp, visible, Sp, To, Sp, visible, Comma, Esc,
            ptq, Colon, Sp, residual, Sp, To, Sp, visible, Comma, Esc,
            qtp, Colon, Sp, visible, Sp, To, Sp, residual, Comma, Esc,
            qtq, Colon, Sp, residual, Sp, To, Sp, residual, Dot));
    }

    private static Formula OrthogonalDecompositionFormula()
    {
        Formula visible = F.Id("V");
        Formula projection = F.Id("P");
        Formula complement = F.Id("Q");
        Formula map = F.Id("T");

        return Disp(Seq(
            OpenBracket, Call("HasOrthogonalProjection", visible), CloseBracket,
            Comma, Sp, complement, Sp, Eq, Sp, Subtract(D(1), projection),
            Sp, Rightarrow, Sp,
            Equal(map, FourBlockSum(projection, complement, map)), Dot));
    }

    private static Formula CommutatorFormula()
    {
        Formula projection = F.Id("P");
        Formula complement = F.Id("Q");
        Formula map = F.Id("T");
        Formula commutator = Subtract(
            Multiply(projection, map),
            Multiply(map, projection));
        Formula crossTerms = Subtract(
            Product(projection, map, complement),
            Product(complement, map, projection));

        return Disp(Seq(
            Equal(complement, Subtract(D(1), projection)), Sp, Rightarrow, Sp,
            Equal(commutator, crossTerms), Dot));
    }
}
