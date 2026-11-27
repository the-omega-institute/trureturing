using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2GroundChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed ground modes and neutral zero modes reduce charges and first oscillators.",
        H("Ground Charge Descent in the Fixed Lattice Quotient"),
        Blocks(
            Paragraph(Text("The first-oscillator calculation uses the actual neutral quadratic zero modes "
                + "and translation, following the rank-one calculations of Yamskulna "
                + "(arXiv:math/0202056, section 4).")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-ground-two-orbit-relation"),
                DeclarationHandle.Create(Prefix + "fixed_ground_two_orbit_relation"),
                H("A ground class equals a creation class on the other orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write s for the Gram pairing of a and b and assume s>0. The "
                    + "actual mode at -s-1 of the two fixed ground states has two terms with the "
                    + "same nonzero cocycle factor. The orbit of a+b contributes its ground state, "
                    + "while the orbit of a-b contributes its paired creation coefficient of "
                    + "index 2s. The mode lies in intrinsic C2, so the ground class is the negative "
                    + "of that creation class."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-ground-outside-short-step"),
                DeclarationHandle.Create(Prefix + "fixed_ground_charge_step_outside_short"),
                H("A signed basis step lowers the charge energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a charge γ is outside the closed box defined by "
                    + "|B(e_i,γ)| ≤ G(i,i), choose a signed basis charge a in a violated direction "
                    + "so B(a,γ) is positive. Set s = |B(e_i,γ)| - G(i,i) and δ = γ - 2a. The "
                    + "ground class at γ becomes the negative of the paired creation class at δ, "
                    + "of index 2s with creation direction -a on δ. The squared norm drops by 4s "
                    + "and the charge energy by 2s. Positive definiteness gives nonnegative energy, "
                    + "so this is a strict decrease on natural-valued energies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-zero-mode-ideal"),
                DeclarationHandle.Create(Prefix + "fixed_zero_mode_mem_c2"),
                H("Fixed zero modes preserve the intrinsic C2 span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the commutator of a fixed zero mode with a (-2)-mode, the "
                    + "binomial sum keeps only its index-zero term. The zero mode applied to a C2 "
                    + "generator therefore gives two fixed (-2)-products, one from acting on each "
                    + "factor. Linearity extends preservation to the whole span."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-first-oscillator-class"),
                DeclarationHandle.Create(Prefix + "fixed_first_oscillator_class"),
                H("Neutral zero modes isolate the first charged oscillator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic with basis directions i and j acts on the "
                    + "ground by two terms, each a Gram pairing times a first oscillator. Weight by "
                    + "the j-th coordinate of the charge and sum over j. One term gives the squared "
                    + "norm times the first oscillator in direction i. The other is proportional "
                    + "to translation of the ground and vanishes in fixed C2. For nonzero norm, "
                    + "division expresses the first oscillator class in terms of actual zero modes."))),
                DescribeRole.Theorem))));
}
