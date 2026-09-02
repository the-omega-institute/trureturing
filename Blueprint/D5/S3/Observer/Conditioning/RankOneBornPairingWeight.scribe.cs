using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class RankOneBornPairingWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one Born weight is a trace pairing, and unread measurement is its conditional ensemble.",
        H("Rank-One Born Pairing Weight"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-born-weight-is-a-trace-pairing-with-unread-ensemble"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/RankOneBornPairingWeight."
                        + "rank_one_born_pairing_weight"),
                H("Rank-one Born weight, trace pairing, and unread ensemble"),
                StatementSource.FromAuthor(PairingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite complete family of pairwise orthogonal, self-adjoint "
                            + "idempotent complex projections, and let rho be a positive "
                            + "trace-one matrix. Fix a branch k and rank-one representations "
                            + "P_k = phi phi* and rho = psi psi*.")),
                    Paragraph(Text(
                        "Write p_k for the canonical recordWeight. The three conclusions are "
                            + "p_k = |<phi, psi>|^2, p_k = trace(rho P_k), and unreadState P rho "
                            + "= sum_j p_j conditionalState(P, rho, j). The second equality "
                            + "carries the source's object-role assertion: p_k has scalar trace-"
                            + "pairing type, not projection-matrix or quotient-object type.")),
                    Paragraph(Text(
                        "The first and third leaves directly apply the frozen rank-one reduction "
                            + "and unread weighted-ensemble theorems. The middle leaf unfolds only "
                            + "the canonical recordWeight and bornProbability definitions."))),
                DescribeRole.Theorem))));

    private static Formula PairingFormula()
    {
        Formula n = F.Id("n"), labels = F.Id("K"), index = F.Id("k");
        Formula projection = Projection(index), rho = F.Id("rho");
        Formula phi = F.Id("phi"), psi = F.Id("psi");
        Formula weight = Call("recordWeight", F.Id("P"), rho, index);
        Formula tracePairing = Call("tr", Seq(rho, Sp, projection));
        Formula branchIndex = F.Id("j");
        Formula branchWeight = Call("recordWeight", F.Id("P"), rho, branchIndex);
        Formula conditional = Call("conditionalState", F.Id("P"), rho, branchIndex);
        Formula unread = Call("unreadState", F.Id("P"), rho);

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
                Sp, Land, Sp, weight, Sp, Eq, Sp, tracePairing,
                Sp, Land, RowBreak,
                unread, Sp, Eq, Sp,
                Sum, Underscore, Grp(branchIndex, Sp, InMacro, Sp, labels),
                branchWeight, Cdot, Sp, conditional,
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
