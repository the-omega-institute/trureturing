using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class BornReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one record branch on a rank-one pure state is exactly a squared "
            + "transition modulus.",
        H("Rank-One Born Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                                    "rank-one-pure-state-record-weight-is-a-squared-transition-modulus"),
                DeclarationHandle.Create("D5/S3/Observer/BornReduction.rank_one_pure_state_modulus_square_reduction"),
                H("Rank-one pure-state record weight is a squared transition modulus"),
                StatementSource.FromAuthor(ReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Fix one branch k of a finite family P. If its matrix is the rank-one outer "
                                    + "product of phi, while rho is the rank-one outer product of psi, then the "
                                    + "record weight trace(rho P_k) is exactly the squared modulus of their "
                                    + "transition inner product. No measurement axioms or normalization "
                                    + "hypotheses are consumed; for unit vectors the right-hand side is the Born "
                                    + "branch probability. The equality is exact over the complex numbers, with "
                                    + "no approximation or residual term."))),
                DescribeRole.Theorem
            ))));

    private static Formula ReductionFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Land, Sp,
        Projection(), Eq, RankOne(Varphi), Sp, Land, Sp,
        Rho, Sp, Eq, Sp, RankOne(Psi), Sp, Land, Sp,
        Inner(Varphi, Varphi), Eq, D(1), Sp, Land, Sp,
        Inner(Psi, Psi), Eq, D(1), Sp, Rightarrow, RowBreak, Sp,
        Weight(), Eq,
        Lvert, Sp, Inner(Varphi, Psi), Sp, Rvert, Caret, Grp(D(2)), Dot));

    private static Formula Ambient() => Seq(
        Forall, Sp, F.Id("n"), Comma, Sp, Kappa, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
        CloseBracket, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
        CloseBracket, Comma, RowBreak, Sp,
        Forall, Sp, F.Id("P"), Colon, Sp, Kappa, Sp, To, Sp, MatrixType(), Comma, Esc,
        Rho, Sp, InMacro, Sp, MatrixType(), Comma, Esc,
        F.Id("k"), Sp, InMacro, Sp, Kappa, Comma, Esc,
        Varphi, Comma, Sp, Psi, Sp, InMacro, Sp, VectorType(), Comma, RowBreak, Sp);

    private static Formula MatrixType() => Seq(
        F.Id("M"), Underscore, Grp(F.Id("n")),
        Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula VectorType() => Seq(
        Mathbb, Grp(F.Id("C")), Caret, Grp(F.Id("n")));

    private static Formula RecordPremise() => Seq(
        Operatorname, Grp(F.Id("Record")), Open, F.Id("P"), Close);

    private static Formula Projection() => Seq(
        F.Id("P"), Underscore, Grp(F.Id("k")));

    private static Formula RankOne(Formula vector) => Seq(
        vector, Sp, vector, Caret, Grp(Star));

    private static Formula Inner(Formula left, Formula right) => Seq(
        Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula Weight() => Seq(
        F.Id("w"), Underscore, Grp(F.Id("k")), Open, Rho, Close);
}
