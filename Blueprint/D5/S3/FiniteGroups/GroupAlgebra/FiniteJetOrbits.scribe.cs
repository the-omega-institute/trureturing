using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class FiniteJetOrbitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient of the entire normalized original representation family has the weighted divisor cardinality.", H("The actual original representation quotient"), Blocks(
            Describe.Lean(
                DescribeId.Create("finitejetorbits-quotientequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetOrbits.quotientEquiv"),
                H("The actual original representation quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The objects of OriginalFamily are actual Representation F (Multiplicative K) (Polynomial.degreeLT K p) values arising from every normalized F-linear q. They carry no chosen coefficients. The equivalence relation admits any original additive relabeling phi and any invertible merely F-linear P satisfying the original intertwining equation. Identity, inverse and composition of these original maps prove the setoid laws.")),
                    Paragraph(Text("For a prime-field algebra equivalence e:K to L, where L lies in Type, the quotient of this actual representation family is equivalent to WeightedSemilinear.Orbits on L^Fin(n-1). The action is exactly (c,sigma) A_i=c^(-w_i) sigma(A_i), w_i=p^(i+1)-p+1. Algebra transport sends units by e and automorphisms by conjugation; it preserves the full action, rather than just the orders of the automorphism groups. Unique coefficients cover all original q, and the fixed-phi classification proves both directions of the orbit correspondence.")),
                    Paragraph(Text("The native weighted source accepts fields in Type and a separate universe for the coordinate index. For an original K in any universe the final theorem explicitly takes L=Shrink K and uses Shrink.algEquiv over the actual F. This finite-field algebra transport is the precise universe bridge. The original representation quotient stays on K and the original polynomial space throughout."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finitejetorbits-original-class-cardinality"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteJetOrbits.original_class_cardinality"),
                H("The actual original representation quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every odd prime p, including three, n at least one, and the original finite field K with cardinality p^n, the rational cast of the cardinality of OriginalClasses equals (1/n) times sum over d dividing n of totient(n/d)/(p^d-1), multiplied by sum over m dividing p^d-1 of totient(m) p^(d a_m). Here a_m is the number of i in Fin(n-1) such that m divides w_i. Every division takes place in the rationals.")),
                    Paragraph(Text("The equality follows from the actual quotient equivalence and the already proved WeightedSemilinear.orbit_cardinality. There is no orbit-count premise, no no-derivation premise, and no replacement of the original equivalence relation by a restricted semilinear input condition. The original pair source and the actual weighted action remain connected through this endpoint.")),
                    Paragraph(Text("The full coordinate space is used, including the zero tuple, the empty index set when n=1, and every partial-zero support. A field automorphism and multiplication by a nonzero scalar power preserve exactly which coordinates vanish. No freeness or faithfulness condition is imposed. For n=1 the unique normalized original representation gives one class. The factors p^(d a_m) count all solutions, including zero, so support strata are not discarded.")),
                    Paragraph(Text("The new formal integration connects the arbitrary-field representation rigidity theorem, the reused finite-field linearized basis, the normalized coefficient equivalence and the native weighted orbit count. The statement counts this normalized original family, not all representations of the same group and dimension."))), DescribeRole.Theorem))));
}
