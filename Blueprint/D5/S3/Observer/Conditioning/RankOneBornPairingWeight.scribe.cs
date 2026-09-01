using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class RankOneBornPairingWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one branch weight is a nonnegative state-projection pairing equal to a squared transition modulus.",
        H("Rank-One Born Pairing Weight"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-born-weight-is-a-nonnegative-state-projection-pairing"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/RankOneBornPairingWeight."
                        + "rank_one_born_pairing_weight"),
                H("Rank-one Born weight is a nonnegative pairing scalar"),
                StatementSource.FromAuthor(PairingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite complete family of pairwise orthogonal, self-adjoint "
                            + "idempotent complex projections, and let rho be a positive "
                            + "trace-one matrix. Fix a branch k and rank-one representations "
                            + "P_k = phi phi* and rho = psi psi*.")),
                    Paragraph(Text(
                        "Write p_k for the canonical recordWeight, definitionally the complex "
                            + "scalar trace(rho P_k). The first conclusion is exactly "
                            + "p_k = |<phi, psi>|^2. The second conclusion is 0 <= p_k, so the "
                            + "formal carrier is a nonnegative state-projection pairing scalar, "
                            + "not a projection matrix or a quotient object.")),
                    Paragraph(Text(
                        "The equality directly applies the frozen rank-one reduction. "
                            + "Nonnegativity directly applies the canonical Born probability "
                            + "skeleton to the positive trace-one state and the selected record "
                            + "projection."))),
                DescribeRole.Theorem))));

    private static Formula PairingFormula()
    {
        Formula n = F.Id("n"), labels = F.Id("K"), index = F.Id("k");
        Formula projection = Projection(index), rho = F.Id("rho");
        Formula phi = F.Id("phi"), psi = F.Id("psi");
        Formula weight = Call("tr", Seq(rho, Sp, projection));

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, labels, Comma, Sp,
            Call("Fintype", n), Comma, Sp, Call("Fintype", labels), Comma,
            RowBreak, Grp(),
            Forall, Sp, F.Id("P"), Colon, Sp, labels, Sp, To, Sp, MatrixType(n),
            Comma, Sp, rho, InMacro, Sp, MatrixType(n), Comma, Sp,
            index, InMacro, Sp, labels, Comma, Sp,
            phi, Comma, Sp, psi, InMacro, Sp, VectorType(n), Comma,
            RowBreak, Grp(),
            Call("Record", F.Id("P")), Sp, Land, Sp,
            Call("PosSemidef", rho), Sp, Land, Sp,
            Call("tr", rho), Sp, Eq, Sp, D(1), Sp, Land, RowBreak,
            projection, Sp, Eq, Sp, RankOne(phi), Sp, Land, Sp,
            rho, Sp, Eq, Sp, RankOne(psi), Sp, Rightarrow, RowBreak,
            Open,
                weight, Sp, Eq, Sp,
                Lvert, Inner(phi, psi), Rvert, Caret, Grp(D(2)),
                Sp, Land, Sp, D(0), Sp, Leq, Sp, weight,
            Close, Dot));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula VectorType(Formula n) => Seq(
        Mathbb, Grp(F.Id("C")), Caret, Grp(n));

    private static Formula Projection(Formula index) =>
        Seq(F.Id("P"), Underscore, Grp(index));

    private static Formula RankOne(Formula vector) =>
        Seq(vector, Sp, vector, Caret, Grp(Star));

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
}
