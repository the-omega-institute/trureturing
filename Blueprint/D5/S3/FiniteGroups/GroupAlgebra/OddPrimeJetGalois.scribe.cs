using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetGaloisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual original-label Galois projection and derived-series bounds.", H("Actual Galois image and derived bounds"), Blocks(
            Describe.Lean(DescribeId.Create("odd-prime-jet-original-galois"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois.originalGalois"),
                H("The actual original-label Galois projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual original pair z=(P,phi), let c be phi(1), interpreted in the original additive field. The unique field automorphism sigma satisfying phi(a)=c sigma(a) is its Galois coordinate. Classification supplies sigma, and c is nonzero. Uniqueness follows by cancellation of c. Composition of the actual labels gives a homomorphism gamma from the actual original group into Gal(K/F). Its range is the actual Galois image. This definition makes no choice of a lift of a Galois element."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-jet-original-derived-three"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois.original_derived_three_eq_bot"),
                H("The third actual derived subgroup is trivial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd prime, finite field K of order p^n in its arbitrary universe, n at least one, and normalized unrestricted prime-field-linear q, the third derived subgroup of the actual original group is trivial. The actual Galois group is cyclic, so the first derived subgroup lies in the Galois kernel. On that kernel the action on the constant line is an ordinary field scalar, and the original label is another field scalar. These two actual readouts form a homomorphism into K* times K*. An element in its kernel has identity label and leading constant scalar one, hence lies in the actual principal units. Consequently the second derived subgroup lies in those principal units, which are abelian. The constant-line action is obtained from the actual coherent label lift and the actual commutant normal form. No splitting of the label stabilizer onto its Galois image is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-original-derived-two-trivial-image"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois.original_derived_two_of_galois_trivial"),
                H("Trivial actual Galois image implies metabelianity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the actual Galois image is trivial, both scalar readouts are defined on the entire actual original group. Its first derived subgroup therefore lies in the abelian actual principal-unit subgroup, and its second derived subgroup is trivial. This implication does not assert the converse."))), DescribeRole.Theorem))));
}
