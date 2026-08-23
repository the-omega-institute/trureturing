using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class ScaleDefectCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent projections through an intermediate scale obey the Lipschitz diagonal-defect bound.",
        H("Diagonal Defect Across Three Scales"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-scale-defect-composes"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/ScaleDefectComposition."
                        + "diagonal_scale_defect_comp_le"),
                H("Diagonal scale defects compose"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k <= i <= j be three scales. Each scale has a table carrier T_s, "
                            + "an output carrier U_s, and a diagonal map Delta_s. The table "
                            + "projections P and output projections Q are typed separately.")),
                    Paragraph(Text(
                        "The direct projections are publicly required to equal the composites "
                            + "P_(i,k) after P_(j,i) and Q_(i,k) after Q_(j,i). Output carriers "
                            + "at i and k carry the pseudometrics used by the three defects.")),
                    Paragraph(Text(
                        "If Q_(i,k) is L-Lipschitz, insert Q_(i,k) Delta_i P_(j,i)(E) between "
                            + "the endpoints. The metric triangle inequality and the Lipschitz "
                            + "distance bound give L times the j-to-i defect plus the i-to-k "
                            + "defect at P_(j,i)(E).")),
                    Paragraph(Text(
                        "The pointwise defect is imported from the frozen diagonal-naturality "
                            + "family and is exactly dist(Q Delta(E), Delta(P(E))). Pinned "
                            + "Mathlib supplies dist_triangle and LipschitzWith.dist_le_mul."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula first, Formula second) =>
        Seq(value, Underscore, Grp(first, Comma, second));

    private static Formula At(Formula family, Formula index) =>
        Seq(family, Underscore, Grp(index));

    private static Formula Defect(
        Formula tableProjection,
        Formula outputProjection,
        Formula highDiagonal,
        Formula lowDiagonal,
        Formula input) =>
        Call("naturalityDefect", tableProjection, outputProjection,
            highDiagonal, lowDiagonal, input);

    private static Formula MainFormula()
    {
        Formula scale = F.Id("S");
        Formula table = F.Id("T");
        Formula output = F.Id("U");
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula delta = F.Id("Delta");
        Formula pji = Indexed(p, j, i);
        Formula pik = Indexed(p, i, k);
        Formula pjk = Indexed(p, j, k);
        Formula qji = Indexed(q, j, i);
        Formula qik = Indexed(q, i, k);
        Formula qjk = Indexed(q, j, k);
        Formula deltaJ = At(delta, j);
        Formula deltaI = At(delta, i);
        Formula deltaK = At(delta, k);
        Formula input = F.Id("E");
        Formula l = F.Id("L");

        return Disp(Seq(
            Forall, Sp, scale, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Preorder")), Open, scale, Close,
            CloseBracket, Comma, Esc,
            table, Comma, Sp, output, Colon, Sp,
            new Formula.TypeArrow(scale, Seq(Operatorname, Grp(F.Id("Type")))), Comma, Esc,
            k, Comma, Sp, i, Comma, Sp, j, Colon, Sp, scale, Comma, Sp,
            input, Colon, Sp, At(table, j), Comma, Sp,
            l, Colon, Sp, Operatorname, Grp(F.Id("NNReal")), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")),
            Open, At(output, i), Close, CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")),
            Open, At(output, k), Close, CloseBracket, Comma, Esc,
            k, Sp, Leq, Sp, i, Sp, Leq, Sp, j, Comma, Esc,
            pji, Colon, Sp, new Formula.TypeArrow(At(table, j), At(table, i)), Comma, Sp,
            pik, Colon, Sp, new Formula.TypeArrow(At(table, i), At(table, k)), Comma, Sp,
            pjk, Colon, Sp, new Formula.TypeArrow(At(table, j), At(table, k)), Comma, Esc,
            qji, Colon, Sp, new Formula.TypeArrow(At(output, j), At(output, i)), Comma, Sp,
            qik, Colon, Sp, new Formula.TypeArrow(At(output, i), At(output, k)), Comma, Sp,
            qjk, Colon, Sp, new Formula.TypeArrow(At(output, j), At(output, k)), Comma, Esc,
            deltaJ, Colon, Sp, new Formula.TypeArrow(At(table, j), At(output, j)), Comma, Sp,
            deltaI, Colon, Sp, new Formula.TypeArrow(At(table, i), At(output, i)), Comma, Sp,
            deltaK, Colon, Sp, new Formula.TypeArrow(At(table, k), At(output, k)), Comma, Esc,
            pjk, Sp, Eq, Sp, pik, Sp, Circ, Sp, pji, Sp, Land, Sp,
            qjk, Sp, Eq, Sp, qik, Sp, Circ, Sp, qji, Sp, Land, Sp,
            Call("LipschitzWith", l, qik), Sp, Rightarrow, RowBreak,
            Defect(pjk, qjk, deltaJ, deltaK, input), Sp, Leq, Sp,
            l, Sp, Cdot, Sp, Defect(pji, qji, deltaJ, deltaI, input), Sp, Plus, RowBreak,
            Defect(pik, qik, deltaI, deltaK, Seq(pji, Open, input, Close)), Dot));
    }
}
