using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class PowerAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Repeating a finite nonnegative experiment n times multiplies its Renyi divergence exactly by n at every real order, without normalization.",
        H("Power Additivity of Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-renyi-divergence-is-additive-on-iid-powers"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/PowerAdditivity.renyi_divergence_power_additive"),
                H("Finite Renyi divergence is additive on i.i.d. powers"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    Operatorname, Grp(F.Id("iidPower")),
                    Open, F.Id("p"), Comma, Sp, F.Id("n"), Close,
                    Vert, Sp, Vert, Sp,
                    Operatorname, Grp(F.Id("iidPower")),
                    Open, F.Id("q"), Comma, Sp, F.Id("n"), Close, Close,
                    Eq, RowBreak,
                    F.Id("n"), Sp, Cdot, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Repeating an experiment n times multiplies its Renyi divergence by " +
                        "exactly n. This identity is a prerequisite for sample-complexity " +
                        "statements: it converts the distinguishability of two single-trial " +
                        "laws into the number of independent trials required to distinguish " +
                        "their repeated observations.")),
                    Paragraph(Text(
                        "The encoding is chosen so that induction consumes the frozen binary " +
                        "theorem directly. IidSpace is a recursive right-associated product: " +
                        "IidSpace iota 0 is PUnit, while IidSpace iota (n+1) is iota times " +
                        "IidSpace iota n; iidPower assigns mass one to the empty product and " +
                        "the corresponding product mass at a successor. Consequently, the " +
                        "successor sample type and mass are definitionally in the product shape " +
                        "accepted by renyi_divergence_product_additive. The conventional " +
                        "alternative Fin n -> iota requires no new definitions, but it would " +
                        "require every finite sum to be re-indexed through Fin.consEquiv before " +
                        "the binary theorem could apply. Two minimal definitions were judged " +
                        "cheaper than a re-indexing at every step. The induction therefore " +
                        "applies the frozen theorem directly rather than re-deriving additivity.")),
                    Paragraph(Text(
                        "The final theorem requires strictly less than the theorem on which its " +
                        "induction depends. Binary additivity requires both marginal power sums " +
                        "to be nonzero, whereas the n-fold statement assumes only pointwise " +
                        "nonnegativity of p and q. The separately stated, load-bearing power-sum " +
                        "lemma identifies the n-copy power sum with the n-th power of the " +
                        "single-trial power sum. When the base is nonzero, pow_ne_zero supplies " +
                        "the non-vanishing premise needed by the frozen binary theorem; when the " +
                        "base is zero, the complementary branch is settled directly. Both " +
                        "branches are internal to the proof, so no power-sum hypothesis survives " +
                        "in the theorem statement.")),
                    Paragraph(Text(
                        "The zero-copy case is clean. IidSpace iota 0 is PUnit, iidPower is the " +
                        "empty product of value one, and its power sum is one. The left side is " +
                        "therefore (1/(alpha-1)) times log 1 = 0, while the right side is zero " +
                        "times D_alpha(p,q) = 0. Neither non-vanishing nor normalization is " +
                        "consumed in this case.")),
                    Paragraph(Text(
                        "The freedoms of the binary theorem are inherited without narrowing: " +
                        "alpha may be any real number, and neither p nor q is required to be " +
                        "normalized. Thus the n-fold theorem introduces no order restriction " +
                        "and no probability-mass requirement beyond the stated pointwise " +
                        "nonnegativity.")),
                    Paragraph(Text(
                        "No sample-complexity corollary, order-one limit, measure-theoretic " +
                        "analogue, or theorem for non-identical factors is claimed. Products of " +
                        "non-identical factors remain the territory of the frozen binary " +
                        "additivity theorem."))),
                DescribeRole.Theorem))));
}
