using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class SymmetricPowerTranslationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quotient symmetric powers and their contragredients acquire polynomial translation coordinates in every degree.",
        H("Genuine symmetric powers in translation coordinates"),
        Blocks(
            Paragraph(Text("Let K be a field, V a K-vector space with a basis b indexed by Fin 2, and n a natural number. The source is the actual Mathlib quotient SymmetricPower K (Fin n) V. Its map to K[z] sends a pure tensor of vectors v_j to the product of the linear polynomials whose coordinates send b(0) to 1 and b(1) to z. The image lies in degree less than n+1.")),
            Paragraph(Text("The current Mathlib quotient shares its coefficient-ring and index universes: the literal index Fin n therefore requires K : Type here. V and the additive group E keep independent universes. This API boundary is explicit; it is not a finite-field, factorial, characteristic or degree restriction.")),
            Describe.Lean(
                DescribeId.Create("symmetric-power-polynomial-coordinates"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.polynomialEquiv"),
                H("The actual quotient and bounded polynomials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/elmerkadr2025relative")),
                Blocks(
                    Paragraph(Text("For every basis b and natural n, polynomialEquiv is a K-linear equivalence from SymmetricPower K (Fin n) V to the polynomials of degree less than n+1. No averaging or division by n! is used. The result includes n=0 and n greater than or equal to the characteristic.")),
                    Paragraph(Text("The construction descends the symmetric multilinear product through the actual additive-congruence quotient. Basis tensors span the quotient. Two words in the two basis vectors with the same number of occurrences of b(1) are related by an actual permutation of Fin n and hence have the same quotient class. The inverse sends the monomial z^i to a representative word with i occurrences of b(1). The two composites are proved to be identities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-power-faithful-models"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.exists_faithful_polynomial_models"),
                H("One parameter for every actual symmetric power and dual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/elmerkadr2025relative")),
                Blocks(
                    Paragraph(Text("Now let E be a nontrivial additive commutative group of exponent p, where p is prime and char K=p. Let V have finrank two and let rho be an injective representation of Multiplicative E on V. There exists one injective additive alpha:E->K such that, for every natural n, both the actual degree-n symmetric-power representation and its ordinary contragredient are equivariantly isomorphic to the primal and dual polynomial translation models of dimension n+1 restricted along alpha.")),
                    Paragraph(Text("The theorem obtains b and both action equations from exists_faithful_unipotent_basis. Its caller supplies no basis, alpha, polynomial-coordinate equation or desired equivalence. Equivariance of the primal quotient map follows on pure tensors and then on their span. For the contragredient, pull back by the inverse primal equivalence and use the inverse group element: the resulting dual action evaluates a polynomial at z-alpha(e). This fixes the sign without imposing a separate dual-action hypothesis."))),
                DescribeRole.Theorem),
            Paragraph(Text("At every positive original index i, the original dual module is the dual of SymmetricPower K (Fin (i-1)) V. Thus Sym^0 occurs at i=1; it is not the zero module V_0 of the polynomial extension. OriginalWClassification consumes the actual positive-index equivalences for its literal direct sums and tensors. The construction is the classical coordinate model underlying Elmer--Kadr Section 2.2, not a novelty or full open-problem resolution claim.")))));
}
