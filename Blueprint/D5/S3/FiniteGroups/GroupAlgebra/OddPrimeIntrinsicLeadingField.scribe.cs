using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeIntrinsicLeadingFieldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict rank bound forces the intrinsic leading algebra of an actual odd-prime representation to be a field.",
        H("A field on the intrinsic first augmentation layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-prime-intrinsic-leading-field"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingField.intrinsic_leading_field"),
                H("Two evaluations exclude every common proper subspace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be any odd prime, K any finite field of characteristic p, and f=finrank over ZMod p of K "
                        + "for its canonical prime-field algebra. Let r,m be positive, V any finite-dimensional K-space "
                        + "of dimension p*m, with field and vector-space universes independent, and rho any actual representation of Multiplicative (Fin r -> ZMod p) on V. "
                        + "Every actual cyclic subgroup restriction is assumed projective. Independently, for every list xs "
                        + "of length p, the ordered List.prod of the operators rho(ofAdd g)-1 along xs is assumed zero; "
                        + "repetitions and every ordering remain in scope. Fix any actual h != 1 and assume r > f*(m/2), "
                        + "where m/2 is natural-number division.")),
                    Paragraph(Text(
                        "Put U=Representation.Coinvariants rho and q=Representation.Coinvariants.mk rho. "
                        + "The intrinsic leading action gives an Fp-linear A from Fin r -> ZMod p to End_K(U), "
                        + "with dim_K U=m, A(h.toAdd)=1, every nonzero A(g) a unit, and pairwise commuting A(g). "
                        + "Retain exactly its intrinsic certificate: A(g)(q(v))=q(w) if and only if "
                        + "(rho(ofAdd g)-1)(v)-(rho(h)-1)(w) lies in range (rho(h)-1)^2. "
                        + "No coefficient model is an input.")),
                    Paragraph(Text(
                        "Suppose W is a nonzero proper K-subspace invariant under every A(g), and write d=dim_K W. "
                        + "Choose w != 0 in W and a nonzero class q0 in U/W. Restrict A(g) to B(g) on W. "
                        + "For g != 0, the unit A(g) makes B(g) injective. Since W is finite-dimensional, "
                        + "LinearMap.injective_iff_surjective makes B(g) surjective. Therefore W.map(A(g))=W. "
                        + "This equality is used to prove quotient injectivity: if A(g)v belongs to W, choose w' in W "
                        + "with A(g)w'=A(g)v, then ambient injectivity gives w'=v. Thus v belongs to W. "
                        + "The induced Q(g) on U/W has zero kernel and is a unit by the existing finite-dimensional API.")),
                    Paragraph(Text(
                        "The additive evaluations g |-> B(g)w and g |-> Q(g)q0 become Fp-linear by "
                        + "AddMonoidHom.toZModLinearMap. If either evaluates to zero for a nonzero g, injectivity of B(g) "
                        + "or Q(g) contradicts the chosen nonzero vector or quotient class. Applied to differences, this "
                        + "proves both evaluation maps injective. LinearMap.finrank_le_finrank_of_injective and "
                        + "Module.finrank_mul_finrank give r<=f*d and r<=f*dim_K(U/W). "
                        + "Submodule.finrank_quotient_add_finrank identifies dim_K(U/W)=m-d. Hence "
                        + "r<=f*min(d,m-d)<=f*(m/2), contradicting the strict hypothesis. "
                        + "The two bounds exclude every common nonzero proper invariant subspace.")),
                    Paragraph(Text(
                        "Let C=Algebra.adjoin K (Set.range A), inside the actual End_K(U). "
                        + "Algebra.isMulCommutative_adjoin supplies commutativity. Restrict the existing "
                        + "Module.End.applyModule evaluation action through C.val.toRingHom using Module.compHom; "
                        + "Module.End.apply_faithfulSMul supplies faithfulness after the inclusion. "
                        + "Each C-submodule restricts to an A-invariant K-subspace, so the proved obstruction gives "
                        + "IsSimpleModule C U. IsSimpleModule.annihilator_isMaximal, Module.annihilator_eq_bot and "
                        + "Ring.isField_iff_maximal_bot then give IsField C. This identifies the actual generated subalgebra as a field.")),
                    Paragraph(Text(
                        "A local use of IsField.toField permits the existing isSimpleModule_iff_finrank_eq_one: "
                        + "U has rank one over C. The tower law gives finrank K C=m. For a nonzero u in U, "
                        + "the existing singleton-span kernel and simple-module surjectivity theorems make "
                        + "evaluation c |-> c(u) a K-linear equivalence C equiv_K U. The public output records "
                        + "IsField C, its degree m, and this actual evaluation equivalence.")),
                    Paragraph(Text(
                        "The finite-field cyclic-projectivity lower bound is dim_K(V) >= p*ceil(r/f), with f>0. "
                        + "If dim_K(V) attains this bound, then m=ceil(r/f). The ceiling convention gives "
                        + "f*(m-1)<r<=f*m; since m>0, floor(m/2)<=m-1. Thus f*floor(m/2)<r. "
                        + "Under the independent mixed-vanishing hypothesis, exact minimum dimension therefore forces "
                        + "a genuine degree-m extension-field structure on the intrinsic first layer for odd primes. "
                        + "This is an elementary interpretation of the stated strict threshold and the existing lower bound, "
                        + "rather than an additional formal corollary. The characteristic-two non-field example shows "
                        + "why the odd-prime first-layer conclusion has structural significance.")),
                    Paragraph(Text(
                        "The strict threshold is f*floor(m/2), and the odd-prime range includes p=3. "
                        + "Oddness is used in the prior intrinsic extraction to read the degree-two layer; the new "
                        + "subspace argument uses its actual nonsingular commuting output. The field describes the "
                        + "first augmentation layer. Higher augmentation terms are not classified, so no full-action "
                        + "field conjugacy is concluded. Projectivity is not claimed to imply the independent mixed-product "
                        + "hypothesis. No literature priority is asserted."))),
                DescribeRole.Theorem))));
}
