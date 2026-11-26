using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Measure;

internal sealed class NormalizedHolderEqualityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/finner1992holder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality in finite normalized Holder identifies all densities almost everywhere under one arbitrary measure.",
        H("Equality in finite normalized Holder"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalized-holder-equality"),
                DeclarationHandle.Create("D5/S3/Analytic/Measure/NormalizedHolderEquality.lintegral_prod_rpow_eq_one_iff"),
                H("A finite family under an arbitrary measure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let X be any measurable space, mu any measure on X, and J any finite type. " +
                        "For every j in J let q_j:X->ENNReal be mu-almost-everywhere measurable " +
                        "with integral_mu q_j=1. Let the real weights w_j be strictly positive " +
                        "and sum to one. Then integral_mu(product_j q_j(x)^{w_j})=1 if and " +
                        "only if q_j=q_k mu-almost everywhere for every j and k. In particular, " +
                        "measurable functions satisfy the measurability premise. No probability, " +
                        "finite-measure, sigma-finiteness, topology, boundedness or pointwise " +
                        "positivity premise is imposed.")),
                    Paragraph(Text(
                        "The empty type is retained: its weight-sum premise is inconsistent. " +
                        "For a singleton the weight is one and the conclusion reduces to the " +
                        "unit-integral premise. Zeros on sets of positive measure are allowed. " +
                        "A unit integral makes each q_j finite almost everywhere, while infinity " +
                        "on null sets remains allowed. Positivity and the weight sum already " +
                        "imply w_j<=1; no separate upper bound is assumed.")),
                    Paragraph(Text(
                        "The forward proof inducts over the finite family. After isolating one " +
                        "weight a, renormalize the remaining weights by 1-a and call their " +
                        "weighted product g. Finite Holder gives integral_mu g<=1. Saturation " +
                        "of the original product and binary Holder force integral_mu g=1. " +
                        "Induction identifies the remaining densities, and the binary equality " +
                        "criterion identifies the isolated density with g. Their common finite " +
                        "almost-everywhere values make g equal to each remaining density. " +
                        "Conversely, a finite intersection of the almost-everywhere equalities " +
                        "makes the weighted product equal to any one density, using the weight " +
                        "sum and almost-everywhere finiteness.")),
                    Paragraph(Text(
                        "The binary equality supplier is Mathlib's " +
                        "ENNReal.lintegral_mul_eq_one_iff_of_lintegral_rpow_eq_one, applied " +
                        "to q_1^a and q_2^b with conjugate exponents 1/a and 1/b. The other " +
                        "integral suppliers are ENNReal.lintegral_prod_norm_pow_le and " +
                        "ENNReal.lintegral_mul_norm_pow_le. This is a formal derivation of " +
                        "a classical finite Holder equality criterion; no mathematical " +
                        "originality is claimed. The Library note qualifies the literature " +
                        "scope and distinguishes this single-measure criterion from the " +
                        "coordinate-profile classification."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the full Finner equality problem, all factors are defined on the same " +
                "actual product probability law and depend on their prescribed coordinate " +
                "sets. The criterion above can identify normalized factors on a common " +
                "measure once their unit integrals and Holder saturation are established. " +
                "It does not extract one common family of coordinate profiles from equality " +
                "in the entire marginal chain. That classification remains unproved, " +
                "including recovery of every original row across slices with zero " +
                "conditional mass; positivity of the full row integrals supplies no " +
                "additional conditional-positivity premise.")))));
}
