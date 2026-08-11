using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class LeCamTightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Estimation/LeCamTight",
            "An explicit likelihood-comparison test attains Le Cam's finite two-point total-error floor and fixes the optimizing sign by theorem."),
        H("The Explicit Test Attaining Le Cam's Two-Point Bound"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("explicit-negative-gap-test-attains-le-cam-total-error-floor"),
                H("The explicit negative-gap test attains Le Cam's total-error floor"),
                LeanTheorem(
                    "D5/S3/Estimation/LeCamTight.le_cam_two_point_sum_tight"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("A"), Underscore, Grp(Minus), Colon, Eq,
                    Left, OpenBrace,
                    F.Id("i"), InMacro, Sp, Iota, Sp, Mid, Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    Le, Sp, F.Id("q"), Open, F.Id("i"), Close,
                    Right, CloseBrace, Comma, RowBreak,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close,
                    Close, Sp, Land, Sp,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("i"), InMacro, Sp,
                        F.Id("A"), Underscore, Grp(Minus)), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Plus,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("i"), InMacro, Sp,
                        F.Id("A"), Underscore, Grp(Minus), Caret, F.Id("c")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq,
                    D(1), Minus,
                    Operatorname, Grp(F.Id("TV")),
                    Open, F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The preceding Le Cam module proves that no finite test event can " +
                        "reduce total error below one minus total variation. The present module " +
                        "supplies an event whose total error equals that floor. Taken together, " +
                        "the lower bound and the attaining equality determine the optimum: the " +
                        "minimum total error over all finite test events is exactly one minus " +
                        "total variation, rather than merely being bounded below by it. Neither " +
                        "result in isolation establishes this equality of the optimum.")),
                    Paragraph(Text(
                        "The attainment theorem is constructive at the level relevant to a " +
                        "downstream consumer. It names the acceptance region A_- = {i | p(i) <= " +
                        "q(i)} explicitly, instead of asserting only that some optimal event " +
                        "exists. This witness can be instantiated and evaluated without a further " +
                        "choice or extraction argument, and the statement is correspondingly " +
                        "stronger and more useful than a bare existence claim.")),
                    Paragraph(Text(
                        "The sign is the decisive point. The test reports law q on A, so its total " +
                        "error is the total q-mass plus the event gap sum_A p - sum_A q. Minimizing " +
                        "the error therefore requires the gap to be as negative as possible. The " +
                        "absolute-value variational characterization has two attaining events: " +
                        "A_+ = {i | q(i) <= p(i)} gives the positive gap +TV and is the worst test, " +
                        "whereas A_- = {i | p(i) <= q(i)} gives the negative gap -TV and is the " +
                        "optimal test.")),
                    Paragraph(Text(
                        "The Metric module's documentation identifies A_+ as the witness for its " +
                        "absolute-gap theorem. That witness is correct there but has the wrong sign " +
                        "for Le Cam minimization: substituting it would yield (sum q) + TV, the " +
                        "maximum rather than the minimum. The theorem two_point_le_cam_sign_check " +
                        "settles this distinction by the kernel on p = (1/4, 3/4) and q = (3/4, " +
                        "1/4). With total variation 1/2, it asserts both values at once: A_+ gives " +
                        "3/2 = (sum q) + TV, while A_- gives 1/2 = (sum q) - TV. The selected sign " +
                        "is therefore machine-checked and frozen, not supplied by prose.")),
                    Paragraph(Text(
                        "The proof obtains the required sign directly from the frozen identity " +
                        "total_variation_eq_sum_positive. It applies that identity to q and p in " +
                        "reversed order and uses symmetry of total variation. The result expresses " +
                        "TV as the excess sum of q over p on {i | p(i) <= q(i)}, which is exactly " +
                        "the negative p-minus-q gap needed by the optimal test. The complement-sum " +
                        "identity then converts this signed relation into the displayed total-error " +
                        "equality.")),
                    Paragraph(Text(
                        "An alternative route was searched and deliberately declined. Extracting " +
                        "an attaining event through IsGreatest.1 from " +
                        "total_variation_eq_sup_event_gap would produce a witness whose absolute " +
                        "gap equals total variation, but the absolute value does not determine its " +
                        "sign; a separate sign argument would still be necessary. IsGreatest.1 has " +
                        "no consumer anywhere below D5/S3, and this wave did not become its first " +
                        "consumer because the reversed positive-excess identity proves the needed " +
                        "signed statement directly.")),
                    Paragraph(Text(
                        "Neither general tightness theorem assumes coordinatewise nonnegativity, " +
                        "and no proof step uses it. The positive-excess identity itself requires " +
                        "only equality of total mass. Accordingly, le_cam_two_point_sum_mass_tight " +
                        "establishes attainment at the common-mass level, while " +
                        "le_cam_two_point_sum_tight adds unit mass solely to rewrite that common " +
                        "mass as one. This mass-first theorem followed by a normalized corollary " +
                        "mirrors the layering of the lower-bound Le Cam module.")),
                    Paragraph(Text(
                        "No minimax or sample-complexity corollary, multi-point generalization, " +
                        "uniqueness theorem for the optimal test, or measure-theoretic analogue is " +
                        "claimed. The result identifies and verifies one optimal finite event; it " +
                        "does not classify all optimizers or extend beyond the finite two-point " +
                        "setting.")))))));
}
