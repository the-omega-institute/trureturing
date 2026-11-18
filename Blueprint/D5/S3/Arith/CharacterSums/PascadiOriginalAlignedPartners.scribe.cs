using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalAlignedPartnersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual coefficientwise zero-reduction partners have uniformly subpower cardinality, with no nonalignment restriction on the retained original baseline.",
        H("Aligned baselines and all zero-reduction partners"),
        Blocks(
            Paragraph(Text("Keep the actual prime-cube word, oriented middle congruence basis, anchor physical(B,q)=(-w,-t), original units and retained baseline. Alignment means exact integer determinants det(q,base1)=det(q,base2)=0. The endpoint universe S is a finite set of actual ordered integer coordinate pairs, not a freely chosen coefficient set. The prime-p condition is coefficientwise P_e mod p=0, and includes both identically zero integer pencils and nonzero pencils whose coefficients are all divisible by p.")),
            Node("actual_aligned_zero_reduction_partners_subpower_of_small_heights", "Aligned lifting with direct small-height hypotheses",
                "For every epsilon>0, one positive C bounds actual ordered partners by card(S)<=C*p^epsilon under all original word, unit, anchor, coordinate and literal-box hypotheses stated below. Assume alignment of the retained baseline, 1<=J2<=J1, 2X<p^3 and 2Y<p^3. The only additional size hypotheses are 8J1J2<p, 6J1^3<p^3 and J1<=p; there is no M parameter, fifth-power cap or eighth-power large-prime cutoff.",
                "The shared field-alignment argument forces both endpoint determinants to vanish modulo p. The direct determinant bound lifts them to exact integer alignment. The primitive-line argument uses 6J1^3<p^3 to make the original prime-cube root an integer-zero pencil. The coordinate-height integer-zero theorem then counts those actual partners using J1<=p. Horizontal and vertical directions remain included, and no rational-fiber weight is charged."),
            Node("actual_zero_reduction_partners_subpower_seventh", "All zero-reduction partners for the seventh-power assembly",
                "For every epsilon>0, one positive C bounds the complete actual coefficientwise zero-reduction set S by card(S)<=C*p^epsilon, with no alignment premise on its retained baseline. Keep the original word, units, anchor, literal boxes and all coordinate bounds. Besides 1<=J2<=J1 and the literal width bounds, require exactly 8J1J2<p, 6J1^3<p^3 and J1<=p. These are the direct small-height inputs for the seventh-power scale assembly; this theorem does not assume or establish that scale gap itself.",
                "Split on exact integer alignment of the actual baseline. The aligned branch consumes the new small-height theorem. The nonaligned branch retains the same finite coordinate universe, actual word-to-ActualPair map and injection into modularZeroPartners, using only 8J1J2<p. Thus the old fifth-power cap and eighth-power cutoff are absent from both branches. The original public cap-and-cutoff theorem below is retained as a short consequence, and no long counting proof is duplicated."),
            Node("actual_aligned_zero_reduction_partners_subpower", "Aligned original baselines force integer-zero pencils",
                "For every epsilon>0, one positive C counts all actual zero-reduction partners of any aligned retained baseline by card(S)<=C*p^epsilon. The anchor, baseline and endpoints obey the J1,J2 coordinate bounds, every partner satisfies the original word and literal physical box, 2X<p^3 and 2Y<p^3, and 1<=J2<=J1. Retain the original basis, anchor, baseline and shifted-expression units. Require (J1*J2)^5<=M^5*p^3 and (24*(8*18)^4)^5*M^40<p. No rational-fiber weight is charged.",
                "Over the prime field the aligned baseline vectors are scalar multiples u*q and v*q. The actual baseline units imply u+v-1, uv and uv-(u+v-1) are nonzero. The zero-reduction pencil completes to a nonzero scalar multiple of the square of l_q. Comparing its genuine homogeneous quadratic coefficients forces both endpoint determinants with q to vanish, including horizontal and vertical q. The original cutoffs supply the direct small-height hypotheses, including 8J1J2<p, so the actual integer determinants vanish as well. A primitive integer direction expresses q and all four endpoints by scalar multiples of height at most J1. The integer pencil becomes E*l_v^3 with |E|<=6J1^3<p^3. The original prime-cube root and the unit l_v(beta) force E=0. Thus every actual partner has identically zero integer pencil, and the verified integer-zero divisor theorem supplies the count."),
            Node("actual_zero_reduction_partners_subpower", "The complete coefficientwise zero-reduction count",
                "Under the same original units, word, coordinate, literal-box, cap and cutoff hypotheses, card(S)<=C*p^epsilon for every actual coefficientwise zero-reduction partner set S. The retained baseline may be aligned or nonaligned; it is never replaced by an assumed convenient baseline.",
                "For an aligned baseline use the preceding theorem. Otherwise form the actual finite coordinate universe from the first and second projections of S together with both baseline coordinates. Map the original endpoint identity modulo p to construct ActualPair for every member of S. Its actual injection into modularZeroPartners allows direct consumption of original_modular_zero_partner_subpower, whose nonalignment premise is now satisfied in this branch. A single constant chosen before all data covers both branches."),
            Paragraph(Text("The source problem is due to Pascadi. This completes the actual zero-reduction exceptional layer, including nonzero content-p pencils and integer-zero pencils. It does not by itself bound all original six-variable solutions or assert completion of the full conjecture.")))));

    private static DocumentBlock Node(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("pascadi-original-aligned-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))), DescribeRole.Theorem);
}
