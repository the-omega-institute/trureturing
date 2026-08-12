using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class PowerAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeating a finite strictly positive probability law n times multiplies its classical KL divergence exactly by n.",
        H("Power Additivity of Finite Classical KL Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-classical-kl-divergence-is-additive-on-iid-powers"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/PowerAdditivity.kl_divergence_power_additive"),
                H("Finite classical KL divergence is additive on i.i.d. powers"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp,
                                    Mathbb, Grp(F.Id("N")), Comma, RowBreak,
                                    Open,
                                    Open,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Lt, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Lt, F.Id("q"), Open, F.Id("i"), Close, Close,
                                    Close, Sp, Rightarrow, Sp, RowBreak,
                                    F.Id("D"), Open,
                                    Operatorname, Grp(F.Id("iidPower")),
                                    Open, F.Id("p"), Comma, Sp, F.Id("n"), Close,
                                    Vert, Sp, Vert, Sp,
                                    Operatorname, Grp(F.Id("iidPower")),
                                    Open, F.Id("q"), Comma, Sp, F.Id("n"), Close, Close,
                                    Eq, RowBreak,
                                    F.Id("n"), Sp, Cdot, Sp,
                                    F.Id("D"), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Repeating an experiment n times multiplies its classical KL divergence " +
                                        "by exactly n. Together with the repository's testing-error floors, " +
                                        "this identity is the algebraic step that converts a per-trial " +
                                        "divergence bound into one indexed by the sample count.")),
                                    Paragraph(Text(
                                        "The n-fold encoding is reused, not rebuilt. IidSpace and iidPower are " +
                                        "imported from the Renyi power-additivity module that landed one wave " +
                                        "earlier, and this file declares no definition of its own. A second " +
                                        "n-fold encoding would duplicate a source of truth. This import crosses " +
                                        "buckets within S3, as the DivergenceSupport bucket already does when it " +
                                        "imports from the Divergence bucket.")),
                                    Paragraph(Text(
                                        "The interesting finding is negative: the hypothesis shedding proved for " +
                                        "the Renyi n-fold theorem does not occur here. There, the power-sum lemma " +
                                        "handled both the nonzero-base and zero-base branches internally, so no " +
                                        "non-vanishing premise survived into the theorem statement. Classical " +
                                        "divergence has no branch in which failed positivity makes both sides " +
                                        "collapse to a common value. Every successor application of the frozen " +
                                        "binary theorem therefore still needs strict positivity of p, q, " +
                                        "iidPower p n, and iidPower q n. This is a structural asymmetry between " +
                                        "the two divergence families, not a shortcoming of the proof. One " +
                                        "hypothesis is absent: q need not be normalized, because the frozen " +
                                        "binary theorem does not normalize its reference functions. The module " +
                                        "claims only that these are the hypotheses forced by this proof, not " +
                                        "that they are logically minimal under every possible proof strategy.")),
                                    Paragraph(Text(
                                        "Two named propagation lemmas carry the successor step. iid_power_pos " +
                                        "preserves strict positivity through the finite product and discharges " +
                                        "the binary theorem's positivity arguments for the two powered factors. " +
                                        "iid_power_sum_one preserves total mass one and supplies the required " +
                                        "normalization of the powered primary factor. They are the classical " +
                                        "n-fold analogues of the power-sum lemma in the Renyi module, and each is " +
                                        "consumed at its corresponding argument of the binary theorem.")),
                                    Paragraph(Text(
                                        "The zero-copy case is clean. IidSpace iota 0 is PUnit, both empty " +
                                        "products have value one, and the sole summand is log(1/1) = 0. The " +
                                        "right side is zero times the one-copy divergence. Neither normalization " +
                                        "nor positivity is consumed in this case.")),
                                    Paragraph(Text(
                                        "No sample-complexity corollary is yet claimed; composing this theorem " +
                                        "with the testing-error floors is a separate step. No order-one " +
                                        "connection to the Renyi family, measure-theoretic analogue, or theorem " +
                                        "for non-identical factors is claimed. Products of non-identical factors " +
                                        "remain the territory of the frozen binary theorem."))),
                DescribeRole.Theorem
            ))));
}
