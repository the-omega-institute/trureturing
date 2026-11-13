using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetStabilizerArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic divisor constraint on actual odd-prime jet labels.",
        H("Arithmetic of the actual jet label stabilizer"), Blocks(
            Describe.Lean(DescribeId.Create("oddprimejetgroup-label-divisor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.labelGroup_card_dvd_weighted_ambient"),
                H("The stabilizer divisor constraint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite field K of order p^n over F=ZMod p, the actual label stabilizer is identified with a subgroup of the weighted semilinear group Kˣ ⋊ Gal(K/F). Lagrange's theorem therefore gives |labelGroup(q)| dividing (p^n−1)n. This is the arithmetic restriction on label symmetries; the unrestricted commutant factor is separate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("oddprimejetgroup-full-divisor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_dvd_weighted_ambient"),
                H("The full jet-group divisor constraint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Combining the exact full-group count with the stabilizer divisor constraint gives |G(q)| dividing (p^n−1)p^(n(p−2)+n²)(p^n−1)n. The result is intended for subsequent orbit-size and exceptional-symmetry arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("oddprimejetgroup-primitive-rigidity"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.labelGroup_subsingleton_of_primitive_coordinates"),
                H("Primitive-coordinate rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When n≥3, A(0)=1, and A(1) generates Kˣ by powers, the weight-one equation kills the scalar part of every stabilizing label. The second coordinate then fixes a generator, hence the entire field automorphism; the label formula makes every actual label the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("oddprimejetgroup-primitive-exact-order"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_of_primitive_coordinates"),
                H("Exact order on the primitive stratum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The trivial label stabilizer removes the label factor from the full count, yielding |G(q)|=(p^n−1)p^(n(p−2)+n²). This is the exact generic group order supplied by the weighted action."))),
                DescribeRole.Theorem))));
}
