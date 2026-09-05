using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class SpectralSharpnessNegentropyBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral sharpness is bounded by distance from uniform and hence by negentropy.",
        H("The Spectral Sharpness Negentropy Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-sharpness-negentropy-budget"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/SpectralSharpnessNegentropyBudget."
                    + "spectral_sharpness_negentropy_budget"),
                H("Spectral sharpness is controlled by the entropy deficit"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let r be a probability spectrum on n > 0 points and let u be the "
                        + "uniform spectrum. Spectral sharpness is the repository's attained "
                        + "variational sharpness, equivalently one half of the l1 distance from "
                        + "r to its reversal. The theorem proves Sharp(r) <= 2 TV(r,u) <= "
                        + "sqrt(2(log n - H(r))).")),
                    Paragraph(Text(
                        "The left inequality is the triangle inequality through the fixed point "
                        + "u of reversal; Equiv.sum_comp reindexes the reversed half of the sum. "
                        + "The right inequality is the frozen finite negentropy bound, assembled "
                        + "from Pinsker and the uniform entropy-divergence identity. The frozen "
                        + "maximum-entropy equality proves that u makes both inequalities equalities "
                        + "at zero, supplying the required saturation witness.")),
                    Paragraph(Text(
                        "The source writes mu*(rho) and von Neumann entropy S(rho), while the "
                        + "available frozen interfaces expose spectralSharpness of a finite spectrum "
                        + "and finite Shannon entropy. The statement is therefore made at that "
                        + "precise spectral level. It does not assert an absent density-matrix-to-"
                        + "spectrum entropy bridge, forgetting-channel monotonicity, the qubit "
                        + "fourth-order expansion, a pure-end rank estimate, or numerical trials.")),
                    Paragraph(Text(
                        "Six duplicate routes were checked before formalization: Lean keywords; "
                        + "notation variants including spectralSharpness, muStar, reversal distance, "
                        + "total variation, and entropy deficit; current accepted-event receipts; "
                        + "the digestion backfill by source hash; generalized fixed-point triangle "
                        + "and variational-duality searches; and all in-flight math lanes. The search "
                        + "found the two endpoint theorems but no frozen theorem composing them. The "
                        + "legacy Meta/Digestion/formalizations receipt directory is retired on the "
                        + "current branch; the accepted-event index is its current admission record."))),
                DescribeRole.Theorem))));

    private static Formula BudgetFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula r = F.Id("r");
        Formula u = F.Id("u");
        Formula sharp = Seq(Operatorname, Grp(F.Id("Sharp")));
        Formula tv = Seq(Operatorname, Grp(F.Id("TV")));
        Formula entropy = F.Id("H");

        Formula At(Formula mass, Formula index) => Seq(mass, Open, index, Close);
        Formula Sharp(Formula mass) => Seq(sharp, Open, mass, Close);
        Formula Tv(Formula left, Formula right) =>
            Seq(tv, Open, left, Comma, Sp, right, Close);
        Formula Entropy(Formula mass) => Seq(entropy, Open, mass, Close);
        Formula Deficit(Formula mass) =>
            Seq(Log, Open, n, Close, Minus, Entropy(mass));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            Sp, n, Gt, D(0), Comma, RowBreak,
            r, Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open, n, Close,
            To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            u, Open, i, Close, Eq, n, Caret, Grp(Minus, D(1)), Comma, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, D(0), Le, Sp, At(r, i), Close,
            Sp, Land, Sp, Sum, Underscore, i, At(r, i), Eq, D(1),
            Sp, Rightarrow, RowBreak,
            Sharp(r), Le, D(2), Sp, Tv(r, u), Sp, Land, Esc,
            D(2), Sp, Tv(r, u), Le,
            Sqrt, Grp(D(2), Sp, Open, Deficit(r), Close), Sp, Land, Esc,
            Sharp(u), Eq, D(2), Sp, Tv(u, u), Eq,
            Sqrt, Grp(D(2), Sp, Open, Deficit(u), Close), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
