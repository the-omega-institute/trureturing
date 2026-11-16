using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class RelativePolynomialRetractAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual split polynomial copy absorbs the complementary relative stable class, retaining unrestricted relative-projective witnesses.",
        H("Absorbing the complement of a split polynomial copy"),
        Blocks(
            Paragraph(Text("The live application is the symmetric-power complement extending Elmer--Kadr Lemma 3.8, DOI 10.1007/s13366-026-00855-9. The proof reuses the scalar character of polynomial endomorphisms and its vanishing on the original relative factorization ideal. It does not cancel arbitrary infinite-dimensional modules.")),
            Describe.Lean(
                DescribeId.Create("split-polynomial-retract-relative-absorption"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativePolynomialRetractAbsorption.split_polynomial_retract_absorption"),
                H("The actual complementary projector factors relatively"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be prime and let alpha embed a finite nontrivial additive group E into a field K of characteristic p. Assume N+2<=|E| and that N+1 is nonzero in K. If an arbitrary representation rho is relatively stably isomorphic to the degree-N polynomial dual and contains an actual equivariantly split copy of it, then id-i*r factors through an original M-relative-projective representation. Neither the ambient representation nor the relative-projective factor or its tensor witness is assumed finite-dimensional. For stable maps f,g, the endomorphism f*i is invertible by its nonzero top scalar. Setting u=(f*i)^(-1), D=g*f-id, B=i*u*f-id and Q=id-i*r gives Q*D*B=Q. Sandwiching the original factorization of D proves the claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("intermediate-polynomial-retract-relative-stability"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativePolynomialRetractAbsorption.intermediate_retract_stable"),
                H("An intermediate retract has the same relative class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same polynomial degree, characteristic and embedding assumptions, suppose sigma is an actual equivariant retract of rho and the polynomial copy is an actual equivariant retract of sigma. If rho has the polynomial relative stable class, so does sigma. Both actual splitting identities are premises, not consequences of stable equivalence. This is consumed by the genuine symmetric quotient between a tensor power and its coefficient-sum copy."))),
                DescribeRole.Theorem))));
}
