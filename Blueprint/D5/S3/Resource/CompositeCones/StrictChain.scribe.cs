using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource.CompositeCones;

internal sealed class StrictChainDocument : IScribeDocumentDefinition
{
    private const string LeanDeclaration =
        "D5/S3/Resource/CompositeCones/StrictChain."
        + "strict_composite_cone_chain_and_block_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-qubit separable, positive-semidefinite, and block-positive matrix cones form a strict inclusion chain.",
        H("The Strict Composite Matrix-Cone Chain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-composite-cone-chain-and-block-criterion"),
                DeclarationHandle.Create(LeanDeclaration),
                H("The composite matrix cones form a strict chain"),
                StatementSource.FromAuthor(StrictChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ambient space consists of complex matrices on two two-dimensional "
                            + "factors. The first conjunct says that the separable cone is a proper "
                            + "subset of the positive-semidefinite cone. The second says that the "
                            + "positive-semidefinite cone is a proper subset of the block-positive "
                            + "cone.")),
                    Paragraph(Text(
                        "The final conjunct records the defining product-vector test for block "
                            + "positivity: the real part of the quadratic form is nonnegative for "
                            + "every pair of factor vectors. Thus the displayed theorem includes "
                            + "both strict inclusions and the parenthetical criterion in the source "
                            + "statement.")),
                    Paragraph(Text(
                        "The inclusion proofs are the frozen separable_isPosSemidef and "
                            + "posSemidef_blockPositive declarations. Frozen singlet and exchange "
                            + "operator witnesses establish strictness. Loogle and LeanSearch found "
                            + "the exact Set.ssubset_iff_exists assembly theorem, which the Lean "
                            + "proof applies directly; neither service found an exact theorem for "
                            + "the custom three-cone chain."))),
                DescribeRole.Theorem))));

    private static Formula StrictChainFormula()
    {
        Formula w = F.Id("W");
        Formula matrix = MatrixType();
        Formula factorVector = FactorVectorType();
        Formula separable = SetOf(w, matrix, Call("separableCone", w));
        Formula positive = SetOf(w, matrix, Call("PosSemidef", w));
        Formula blockPositive = SetOf(w, matrix, Call("blockPositive", w));

        return F.Disp(F.Seq(
            F.Open, separable, F.Sp, F.Subset, F.Sp, positive, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, positive, F.Sp, F.Subset, F.Sp, blockPositive, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, F.Forall, F.Sp, w, F.Colon, F.Sp, matrix, F.Comma, F.Sp,
            Call("blockPositive", w), F.Sp, F.Leftrightarrow, F.Sp,
            F.Forall, F.Sp, F.Id("a"), F.Colon, F.Sp, factorVector, F.Comma, F.Sp,
            F.Id("b"), F.Colon, F.Sp, factorVector, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Leq, F.Sp,
            F.Operatorname, F.Grp(F.Id("Re")), F.Open,
            F.Operatorname, F.Grp(F.Id("dotProduct")), F.Open,
            F.Id("a"), F.Times, F.Sp, F.Id("b"), F.Comma, F.Sp,
            w, F.Open, F.Id("a"), F.Times, F.Sp, F.Id("b"), F.Close,
            F.Close, F.Close, F.Close, F.Dot));
    }

    private static Formula SetOf(Formula variable, Formula type, Formula predicate) =>
        F.Seq(F.OpenBrace, variable, F.Colon, F.Sp, type, F.Sp, F.Mid, F.Sp,
            predicate, F.CloseBrace);

    private static Formula Call(string name, Formula argument) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(name)), F.Open, argument, F.Close);

    private static Formula MatrixType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
        FinTwoProduct(), F.Comma, F.Sp, FinTwoProduct(), F.Comma, F.Sp,
        F.Mathbb, F.Grp(F.Id("C")), F.Close);

    private static Formula FactorVectorType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close,
        F.Sp, F.To, F.Sp, F.Mathbb, F.Grp(F.Id("C")));

    private static Formula FinTwoProduct() => F.Seq(
        F.Open, F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close,
        F.Sp, F.Times, F.Sp,
        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close, F.Close);
}
