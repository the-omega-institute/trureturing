using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BhattacharyyaProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Bhattacharyya affinity is multiplicative on finite products under nonnegativity of only the first marginal radicands, consistently with half-order Renyi additivity.",
        H("Bhattacharyya Affinity on Finite Products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bhattacharyya-affinity-is-multiplicative-on-products"),
                DeclarationHandle.Create("D5/S3/TotalVariation/BhattacharyyaProduct.bhattacharyya_product_multiplicative"),
                H("Bhattacharyya affinity is multiplicative on products"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("p"), Apos, Comma, Sp, F.Id("q"), Apos, Colon, Sp,
                    Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("BC")), Open,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    F.Id("p"), Apos, Open, F.Id("j"), Close,
                    Vert, Sp, Vert, Sp,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("q"), Open, F.Id("i"), Close,
                    F.Id("q"), Apos, Open, F.Id("j"), Close,
                    Close, Eq, RowBreak,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Apos, Vert, Sp, Vert, Sp,
                    F.Id("q"), Apos, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Bhattacharyya affinity of a product is the product of the two " +
                        "marginal affinities. Overlap therefore multiplies across independent " +
                        "finite experiments, whereas a distance would add. This is the " +
                        "multiplicative face of the additivity enjoyed by the Renyi family.")),
                    Paragraph(Text(
                        "The hypothesis is unusually weak and records a signature asymmetry, " +
                        "not a symmetric positivity convention. It assumes only that the " +
                        "pointwise product p(i)q(i) is nonnegative. Neither p nor q is required " +
                        "to be nonnegative individually: p(i) = q(i) = -1 satisfies the " +
                        "hypothesis because their product is 1. The second marginal functions " +
                        "p' and q' carry no sign condition at all, and none of the four functions " +
                        "is normalized.")),
                    Paragraph(Text(
                        "This exact hypothesis set is forced by the asymmetric signature of " +
                        "Real.sqrt_mul. That lemma requires nonnegativity only of its first " +
                        "argument. The proof groups each joint radicand as " +
                        "(p(i)q(i))(p'(j)q'(j)), placing the entire sign burden on the first " +
                        "group and leaving the second argument unrestricted. It then exposes " +
                        "the iterated finite sum and factors the two marginal sums with " +
                        "Finset.sum_mul_sum. Nothing was assumed merely for symmetry's sake.")),
                    Paragraph(Text(
                        "The declaration renyi_divergence_product_additive_one_half_consistency " +
                        "is a compiled check rather than a second mathematical result. Taking " +
                        "-2 log of the multiplicativity identity gives exactly product " +
                        "additivity at alpha = 1/2. The declaration states that same half-order " +
                        "equality twice as a conjunction of two identical copies. One conjunct " +
                        "is discharged through the new multiplicativity theorem, together with " +
                        "renyi_divergence_one_half and Real.log_mul; the other is discharged by " +
                        "specializing the frozen general-alpha Renyi additivity theorem to " +
                        "alpha = 1/2.")),
                    Paragraph(Text(
                        "Compiling the conjunction checks that the two independently derived " +
                        "routes agree; disagreement would make the new multiplicativity " +
                        "statement the suspect. The stronger assumptions in the consistency " +
                        "declaration come from the frozen Renyi route: it requires four " +
                        "pointwise nonnegativity hypotheses and non-vanishing of both marginal " +
                        "half-order power sums. The multiplicativity theorem itself needs only " +
                        "nonnegativity of p(i)q(i), so those additional hypotheses belong to " +
                        "the check's frozen-theorem side rather than to the new product law.")),
                    Paragraph(Text(
                        "No n-fold product or i.i.d. form, statement at any other Renyi order, " +
                        "equality characterization, or measure-theoretic analogue is claimed."))),
                DescribeRole.Theorem))));
}
