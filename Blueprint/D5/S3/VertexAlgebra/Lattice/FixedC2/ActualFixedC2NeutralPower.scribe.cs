using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2NeutralPowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A charged ground product lowers the oscillator length of a neutral power.",
        H("Neutral Power Reduction from Charged Ground States"),
        Blocks(
            Paragraph(Text("LatticeData D consists of a natural-number rank and a symmetric integral Gram "
                + "matrix G with even diagonal. For an integer charge tuple a, write B for the integral "
                + "pairing of a with itself and P(a) for the sum of the index-zero oscillators weighted "
                + "by the coordinates of a. Oscillator length counts letters with multiplicity.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-creation-leading-power"),
                DeclarationHandle.Create(Prefix + "creationCoeff_sub_leading_mem"),
                H("The leading oscillator power in a creation coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any D, charge a, and natural n, the n-th creation coefficient "
                    + "minus (1/n!) times P(a)^n lies in the complex span of oscillator words of length "
                    + "at most n-1, with natural-number subtraction. For n=0 the difference is zero. "
                    + "After scaling the coefficient by n!, its recurrence uses the oscillator derivative, "
                    + "which preserves length, and multiplication by P(a), which raises it by at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-ground-minus-three"),
                DeclarationHandle.Create(Prefix + "fixed_ground_minus_three"),
                H("The fixed ground minus-three product is neutral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume B ≥ 4. The (-3)-product of the fixed ground state e^a + e^(-a) "
                    + "with itself equals epsilon(a,a) times the vacuum-charge state whose polynomial is "
                    + "the sum of the creation coefficients for a and -a at index B+2. The doubled-charge "
                    + "terms have negative creation index 2-B and vanish. The cocycle factor is nonzero, "
                    + "so the higher-mode C2 relation kills the class of the sum in the intrinsic quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-power-length-reduction"),
                DeclarationHandle.Create(Prefix + "fixed_neutral_charge_power_length_reduction"),
                H("The charge-polynomial power reduces to shorter even words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume B ≥ 4 and take the natural number k = (B+2).toNat. "
                    + "Evenness of the lattice gives even k. The sum of the creation coefficients for a "
                    + "and -a has leading term (2/k!) times P(a)^k. The class of the sum is zero by the "
                    + "ground product. The fixed projection keeps the even words of the lower-length "
                    + "remainder. Dividing by the nonzero leading coefficient puts the quotient class "
                    + "of the fixed charge-zero state P(a)^k in the complex span of even neutral words "
                    + "of length strictly less than k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-leech-minimum-charge-norm"),
                DeclarationHandle.Create(Prefix + "leech_charge_norm_ge_four"),
                H("The minimum norm in the actual Leech charge coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The charge-coordinate equivalence sends a nonzero charge to a "
                    + "nonzero point of the real Golay-Leech lattice. The integral representative has "
                    + "square sum at least 32, and the integral pairing of the charge with itself is that "
                    + "square sum divided by eight. Thus B ≥ 4 for every nonzero charge of the actual Leech "
                    + "lattice, and the length reduction applies with k = (B+2).toNat."))),
                DescribeRole.Theorem))));
}
