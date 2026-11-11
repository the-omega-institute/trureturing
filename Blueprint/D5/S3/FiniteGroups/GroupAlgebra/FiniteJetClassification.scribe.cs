using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class FiniteJetClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed original additive relabeling forces exactly the inverse weighted coefficient law.", H("Finite original-jet classification"), Blocks(
            Describe.Lean(
                DescribeId.Create("finitejetclassification-fixed-automorphism-coefficients-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetClassification.fixed_automorphism_coefficients_iff"),
                H("Finite original-jet classification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p be any odd prime, including three; n at least one; K a finite field of cardinality p^n with its actual ZMod p algebra structure. Its universe is arbitrary. On the original space V=K[t] of degree less than p take rho_Q(a)=exp(aD+Q(a)D^(p-1)), with the finite exponential and D=d/dt. Fix any automorphism phi of the actual additive group of K. The intertwiner P is an arbitrary invertible F-linear map on V.")),
                    Paragraph(Text("For every A,B in K^Fin(n-1), an intertwiner P rho_A(g)=rho_B(phi(g)) P exists if and only if there are a unit c and an F-algebra automorphism sigma with phi(a)=c sigma(a) for every a and B_i=c^(-w_i) sigma(A_i), where w_i=p^(i+1)-p+1. Neither semilinearity of phi nor global semilinearity of P is an input assumption. The theorem concludes the scalar-semilinear form of this fixed phi; it does not classify all intertwiners P as semilinear.")),
                    Paragraph(Text("The arbitrary-field fixed-automorphism theorem is applied on the actual original actions. Every typed F-derivation delta of the finite field vanishes: Frobenius is surjective, and delta(y^p)=p y^(p-1) delta(y)=0. Hence its derivation term is removed by proof on this field, without an additional no-derivation hypothesis.")),
                    Paragraph(Text("Reference subtraction gives Q_B(c x)-x Q_B(c)=sum_i c^(p^(i+1)) B_i (x^(p^(i+1))-x). Automorphisms preserve these powers and all sums. The unique coefficients of actual normalized functions therefore give c^(p^(i+1)) B_i=c^(p-1) sigma(A_i). Since p^(i+1)=(p-1)+w_i and c is a unit, this is exactly the stated inverse scalar weight. The coefficient of x is minus the sum of the other coefficients on both sides, so no extra equation is lost.")),
                    Paragraph(Text("The converse recovers the full reference-subtracted function identity and then uses the original arbitrary-field sufficiency theorem with delta zero. That theorem preserves the p=3 gauge I-N with inverse I+N+N^2 and uses N^3=0, never the false general assumption N^2=0. All-zero tuples and every partial-zero support remain included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitejetclassification-original-equivalence-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetClassification.original_equivalence_iff"),
                H("Finite original-jet classification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Existentially quantifying the original phi gives equivalence of the original representations exactly when their coefficients lie in one inverse weighted semilinear orbit. For sufficiency the map a maps to c sigma(a) is constructed as an automorphism of the actual additive group. Finite-field normalization and reference subtraction connect this condition to the arbitrary-field pair theorem. No literature-priority claim is made."))), DescribeRole.Theorem))));
}
