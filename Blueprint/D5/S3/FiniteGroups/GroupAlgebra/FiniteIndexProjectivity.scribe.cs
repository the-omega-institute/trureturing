using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class FiniteIndexProjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coset trace detects projectivity when the subgroup index is a unit.",
        H("Projectivity at Finite Index over a Commutative Ring"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-index-projectivity"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/FiniteIndexProjectivity.projective_iff_projective_restrict_of_isUnit_index"),
            H("Projectivity and restriction at unit index"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let R : Type uR be a commutative ring, G : Type uG a group, and V : Type uV an additive commutative group with an R-module structure. For rho : Representation R G V and H : Subgroup G, assume H.FiniteIndex and IsUnit (H.index : R). The statement is Module.Projective R[G] rho.asModule if and only if Module.Projective R[H] (rho.comp H.subtype).asModule. The three universes are independent. The zero ring and zero module remain in scope, as do infinite G, infinite or nonnormal H, and modules with arbitrary generation and presentation.")),
                Paragraph(Text("For descent, Mathlib's restriction functor preserves categorical projective objects via resCoindAdjunction. The equivalence Rep.equivalenceModuleMonoidAlgebra transfers this fact to modules. A universe lift places the module above both the ring and group universes, where the reverse module/category conversion has its required Small instance; an explicit group-algebra linear equivalence then transfers back. Descent itself needs neither finite index nor invertibility.")),
                Paragraph(Text("For ascent, take an arbitrary R[G]-linear surjection f : X -> V. Projectivity of the actual restricted module supplies an R[H]-linear section, hence an R-linear section s satisfying s(h v) = h s(v) for h in H. Define A(g)(v) = g s(g^-1 v). Because (g h)^-1 = h^-1 g^-1 and s is H-equivariant, A(g h) = A(g). Thus A descends to B on the actual left cosets gH, represented in Lean by G ⧸ H with QuotientGroup.leftRel H. No quotient group structure is used.")),
                Paragraph(Text("The covariance is B(x q)(x v) = x B(q)(v), or A(x g)(x v) = x A(g)(v). It follows by cancellation of x^-1 x inside g^-1 x^-1 x; it does not commute group elements. Left translation q -> x q permutes the finite coset space, so T(v) = sum over q in G/H of B(q)(v) is G-equivariant. Each summand satisfies f(B(q)(v)) = v. Consequently f(T(v)) = H.index times v. Only G/H is summed, so neither G nor H needs to be finite.")),
                Paragraph(Text("Choose the actual unit u = hunit.unit in R whose value is (H.index : R). Multiplying T by the value of u^-1 gives an R[G]-linear section because that scalar times (H.index : R) is one. This uses the inverse in R's unit group and makes no field inverse or nonzero-ring assumption. The proof uses the free presentation built into Module.Projective.of_lifting_property'' solely to establish projectivity; it does not assume the original coefficient module is free.")),
                Paragraph(Text("A consequential direct application concerns a finite group G and a prime p with a positive integer a and (p : R)^a = 0. For a p-Sylow subgroup P, put m = P.index. Sylow theory gives gcd(m,p) = 1, hence gcd(m,p^a) = 1. Choose integers u,v with u*m + v*p^a = 1. Casting into R kills the second term and gives an inverse of (m : R). The finite-index theorem therefore reduces R[G]-projectivity to R[P]-projectivity of sigma = rho.comp P.subtype.")),
                Paragraph(Text("The theorem projective_iff_projective_invariants_and_norm_surjective in D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing applies to sigma. In combination, projectivity is characterized by R-projectivity of the actual invariant submodule {v : V | for every h in P, rho(h) v = v} and surjectivity onto that submodule of the actual norm v -> sum over h in P of rho(h) v. Surjectivity here means every P-invariant vector is such a norm, not surjectivity of the norm endomorphism onto all of V. This is exposition of direct reuse, with no additional retained theorem or Describe.")),
                Paragraph(Text("The argument is classical. Nilpotence of (p : R) is the scalar hypothesis for the Sylow application; it does not require the ring to have characteristic p^a. The finite-index theorem itself requires only that the subgroup index cast into R is a unit."))),
            DescribeRole.Theorem))));
}
