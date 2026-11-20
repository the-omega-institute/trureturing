using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class MinimumParityInputsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/MinimumParityInputs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fair subgroup and the active quotient biases give the exact minimum number of input bits.",
        H("The smallest affine independent-bit representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fair-span-eq-spectral-annihilator"),
                DeclarationHandle.Create(Module + ".fairSpan_eq_spectralAnnihilator"),
                H("The nonzero moments determine the fair subgroup"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a finite additive commutative group in which every element added to itself is zero, " +
                    "take any finite family of input columns, an affine offset, and real bias factors. " +
                    "The subgroup spanned by the columns with zero bias equals the subgroup of elements " +
                    "on which every character with a nonzero output moment takes value one. " +
                    "The characters trivial on the fair subgroup descend to the quotient. There is a " +
                    "quotient character distinguishing every nonzero quotient element from zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-offsets-agree-modulo-annihilator"),
                DeclarationHandle.Create(Module + ".signed_offsets_agree_modulo_annihilator"),
                H("The signs determine the adjusted offset on the quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a real mass function on a finite additive commutative group in which every " +
                    "element added to itself is zero. Suppose each of two offsets makes all nonzero " +
                    "moments positive when multiplied by the character value at that offset. Their " +
                    "difference belongs to the subgroup on which all characters with nonzero moments " +
                    "take value one. Indeed, each such character must give the same sign at both offsets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-bias-recovered"),
                DeclarationHandle.Create(Module + ".visibleBias_recovered"),
                H("The quotient moments recover every absolute grouped bias"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take an affine output on a finite additive commutative group in which every " +
                    "element added to itself is zero. For any nonzero column of the quotient by " +
                    "the fair subgroup, invert the logarithms of the absolute moments of the " +
                    "pullback characters. The resulting bias equals the absolute product of the " +
                    "input bias factors whose columns project to that quotient column. Every " +
                    "fair input projects to zero, so the quotient moments used here are nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-input-count-exact"),
                DeclarationHandle.Create(Module + ".minimum_input_count_exact"),
                H("The fair dimension and the active quotient columns give the minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the output space be a finite module over the binary field. Let the " +
                        "real mass function have total mass one and satisfy the quotient criterion " +
                        "for some subgroup and offset. Write H for its spectral annihilator. " +
                        "The number of inputs in every finite affine representation is at least " +
                        "the dimension of H plus the number of nonzero quotient columns whose " +
                        "recovered bias is strictly less than one.")),
                    Paragraph(Text(
                        "There exists a representation with all input biases in the closed " +
                        "interval from -1 to 1, the same mass at every output point, and exactly " +
                        "this many inputs. Fair columns must span H. Distinct active quotient " +
                        "columns require distinct additional inputs. Choose a basis for the fair " +
                        "columns and lift each active quotient column once using its recovered bias " +
                        "to obtain equality."))),
                DescribeRole.Theorem))));
}
