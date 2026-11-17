using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class FiniteJetCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized linear maps on the actual field have unique Frobenius-difference coordinates.", H("Normalized finite-field coefficients"), Blocks(
            Describe.Lean(
                DescribeId.Create("finitejetcoefficients-coefficientmap-bijective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetCoefficients.coefficientMap_bijective"),
                H("Normalized finite-field coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p be a prime, n at least one, and K any finite field in any universe with the given algebra structure over F=ZMod p and cardinality p^n. Put I=Fin(n-1). The normalized space consists of all F-linear maps q:K to K with q(1)=0, with K acting by multiplication in the target. The map from K^I sends A to Q_A(x)=sum_i A_i (x^(p^(i+1))-x). It is bijective and is K-linear. Its inverse is thus defined on every normalized actual function, including zero.")),
                    Paragraph(Text("The single-variable coefficient basis is reused by an Apache-2.0 source adaptation from AxiomMath/CFSG, revision 69cb972f587a3ecc035e092253167ff2e303c962, CFSG/LocalAnalysis/ComponentInitial/FieldFiniteLinearized.lean, particularly finite_field_linearized_linearMap_bases and its single-variable dependencies. The original license is retained in docs/reports/licenses/cfsg-linearized-LICENSE.txt. The adaptation uses the actual given algebra structure and native linear maps, and retains no bilinear API. This imported basis theorem is existing mathematics.")),
                    Paragraph(Text("The reused proof bounds the degree of the linearized polynomial by p^(n-1), strictly below card K, before applying the polynomial root bound. This establishes independence of the actual Frobenius functions. It never infers formal coefficient equality from an arbitrary equality of finite-field functions without a degree bound. The dimension of Hom_F(K,K) over the target K is n, so these n independent maps are a basis.")),
                    Paragraph(Text("Evaluation at one says the sum of all n coefficients is zero. Eliminating the identity-function coefficient leaves exactly n-1 Frobenius differences. Restoring that coefficient as minus the sum gives both existence and uniqueness. If n=1 the tuple is empty and the normalized map is necessarily zero. No coordinate is assumed nonzero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitejetcoefficients-coefficientequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetCoefficients.coefficientEquiv"),
                H("Normalized finite-field coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The bijective coefficient map defines an actual K-linear equivalence K^Fin(n-1) with the normalized submodule of Hom_F(K,K). This equivalence supplies coordinates for every original highest-jet representation and compares the reference-subtracted maps in the finite classification."))), DescribeRole.Definition))));
}
