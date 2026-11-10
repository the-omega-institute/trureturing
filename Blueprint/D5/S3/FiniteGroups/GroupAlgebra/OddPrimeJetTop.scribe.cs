using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetTopDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonidentity Frobenius summands in the actual original kernel.", H("Actual off-diagonal top maps"), Blocks(
            Describe.Lean(DescribeId.Create("odd-prime-jet-top-cardinality"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_cardinality"),
                H("An actual subgroup of order p^(n(n−1))"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be any odd prime, n at least one, and K any finite field in any universe of order p^n with its given F=ZMod p algebra structure. Write Phi(x)=x^p. Every unrestricted F-linear endomorphism has unique linearized coordinates sum_(i<n) a_i Phi^i. The coordinate supplier is the attributed upstream CFSG adaptation in FiniteJetCoefficients. Define W0 by a_0=0, equivalently the direct sum of K Phi^i for 1≤i<n. This condition is neither the vanishing of the ordinary trace nor the condition T(1)=0.")),
                    Paragraph(Text("For every normalized q, the map T↦(1+top(T),identity original label) embeds the additive group of all top maps into the actual kernel of the label projection. Products of two top operators vanish, so multiplication of these units adds T. Uniqueness of the actual commutant coordinates proves injectivity. Restricting the embedding to W0 gives a subgroup with exactly n−1 free K coordinates, hence order p^(n(n−1)). For n=1 it is trivial. This count alone makes no assertion that this subgroup is the commutator subgroup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-top-scalar-range"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.scalar_difference_range"),
                H("Exactly the scalar-action difference image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is one constant field scalar a for which W0 is exactly the image of T↦a T a^(-1)−T. Scalar conjugation multiplies the i-th linearized coefficient by a^(1−p^i), fixing the identity coefficient. Choose a generator of K's multiplicative group. For 1≤i<n, the integer p^i−1 lies strictly between zero and p^n−1, so a^(1−p^i)−1 is nonzero. Dividing each off-diagonal coefficient by this factor gives the converse inclusion, as equality of unrestricted prime-field-linear maps."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-actual-commutator-structure"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.actual_commutator_structure"),
                H("Exact actual kernel commutator subgroup"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The commutator subgroup of the actual label-projection kernel is precisely the embedded W0 top subgroup, of order p^(n(n−1)). To prove the reverse inclusion, expand XY−YX using the actual commutant multiplication formula. The scalar polynomial families and the symmetric top convolution cancel. The remaining top map is a sum of scalar-composition brackets, whose identity-Frobenius coefficients vanish. Right composition by the leading scalars of the two inverse operators preserves W0. Thus the group commutator, obtained by right multiplying XY−YX by X^(-1)Y^(-1) and adding one, is a W0 top unit. The other inclusion is realized by constant-scalar commutators. No section of the label stabilizer onto its Galois image is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-top-derived-inclusion"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_le_commutator"),
                H("Inclusion in the actual kernel commutator subgroup"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual top unit associated to T in W0 belongs to the actual kernel's commutator subgroup. Constant scalar units embed with identity original labels. Their conjugation on top maps is T↦a T a^(-1). Since top products vanish, the commutator with 1+top(S) is exactly 1+top(a S a^(-1)−S). The scalar-action image theorem realizes every T in W0 in this way. Together with the reverse inclusion, this gives the exact subgroup theorem."))), DescribeRole.Theorem)))));
}
