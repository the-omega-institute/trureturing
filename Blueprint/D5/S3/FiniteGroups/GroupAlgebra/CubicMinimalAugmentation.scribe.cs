using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class CubicMinimalAugmentationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/FiniteGroups/GroupAlgebra/CubicMinimalAugmentation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional characteristic-three actual representation case has augmentation quotient two and cubic augmentation nilpotence.",
        H("Cubic minimal augmentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-minimal-augmentation"),
                DeclarationHandle.Create(Prefix + "cubic_minimal_augmentation"),
                H("Kernel-dimension gap at p=3 and rank two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Exact scope: k is ZMod 3, E is the actual group Multiplicative (Fin 2 -> ZMod 3), V is an arbitrary universe-level additive commutative group with k-module and finite-dimensional instances, and rho is an arbitrary actual representation of E on V. The sole hypothesis on rho is that its restriction along every actual cyclic subgroup H, including H equal to the trivial subgroup, is projective over k[H], together with finrank_k V = 6.")),
                    Paragraph(Text(
                        "The theorem returns one conjunction. First, finrank_k (Representation.Coinvariants rho) = 2. Second, for every actual h != 1, the existing coinvariant kernel equals the actual operator range: Coinvariants.ker rho = LinearMap.range (rho h - 1). Third, every ordered list xs of actual group elements with length three has product (xs.map (fun g => rho g - 1)).prod = 0. Repetitions and identity entries are included by the list quantifier.")),
                    Paragraph(Text(
                        "For a nonidentity actual h, orderOf h = 3 by the group exponent calculation. The cyclic restriction is projective, so the cyclic projective dimension identity gives finrank of the h-fixed kernel equal to 2 when finrank V = 6. Since range (rho h - 1) is contained in the coinvariant kernel, this yields the upper bound two for the coinvariant quotient. The cyclic equality is FiniteFieldCyclicDimension.finrank_eq_card_mul_invariants.")),
                    Paragraph(Text(
                        "The lower bound is the kernel-dimension gap. Set A = k[E] and let I be its actual augmentation ideal. Group-algebra linear induction proves that the existing coinvariant projection sends a*x to augmentation(a) times the class of x. This identifies Coinvariants.ker rho with the transport of I times the top A-submodule; the ensuing quotient equivalence identifies Nakayama's quotient with the existing Representation.Coinvariants rho. No replacement coinvariant quotient is introduced. PGroupAugmentation.augmentation_ideal_pow_card gives I^9 = 0, so I lies in the radical of zero and hence in its Jacobson radical. A lift of the one-element quotient basis defines the actual regular-to-rho intertwiner through Representation.leftRegularMapEquiv. Its projection onto the coinvariants is surjective by the one-dimensional spanning lemma. LinearMap.surjective_of_surjective_comp_mkQ then gives surjectivity of the actual A-linear map. The same lemma applied to the zero map excludes zero-dimensional coinvariants when V has dimension six.")),
                    Paragraph(Text(
                        "The regular representation is projective through Representation.ofMulActionSelfAsModuleEquiv and the existing free-module instances. Its restriction is projective by the original FiniteIndexProjectivity.projective_restrict; restriction preserves projectivity without any finite-index hypothesis. There is no index-unit assumption: an index three is not a unit in F3. For every actual cyclic H, equivLinearMapAsModule converts the restricted intertwiner to an A_H-linear surjection. Module.projective_lifting_property supplies a section. The kernel projection is x - s(f(x)); its covariance follows from the intertwining equations, so both inclusion and projection are A_H-linear. Their composite is the identity on the actual intertwining kernel, so Module.Projective.of_split gives its restricted projectivity.")),
                    Paragraph(Text(
                        "The regular carrier has dimension nine by MonoidAlgebra.coeffLinearEquiv and Module.finrank_finsupp_self. Rank-nullity for the surjection gives kernel dimension 9 - 6 = 3 and therefore a nonzero actual E-representation. The existing PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective at p=3 and r=2 forces dimension at least six, a contradiction. This existing endpoint is used because its exact group carrier is Multiplicative (Fin 2 -> ZMod 3); the earlier rank-two endpoint uses Multiplicative (ZMod 3 x ZMod 3). Thus the coinvariant dimension is positive and cannot be one; the upper bound two forces equality.")),
                    Paragraph(Text(
                        "Equal codimensions now identify every actual nonidentity range with the same coinvariant kernel. All augmentation operators commute because E is abelian, and each cube is zero because (rho h - 1)^3 = rho(h)^3 - 1 in characteristic three. Replacing successive range witnesses by the common anchor range moves any ordered triple product onto an anchor cube, so every ordered triple vanishes. The final list assertion is obtained from List.length_eq_three and retains the original product order.")),
                    Paragraph(Text(
                        "The kernel-dimension argument derives mixed vanishing from cyclic projectivity and exact dimension; rho remains an arbitrary actual representation.")),
                    Paragraph(Text(
                        "The numerical obstruction is special to this case. For p >= 5 with rank two at the analogous minimum dimension 2p, the same one-generator construction leaves kernel dimension p^2 - 2p = p(p - 2), which is at least 2p, so the strict contradiction 0 < 3 < 6 disappears. The strict kernel-dimension contradiction therefore applies specifically to characteristic three and rank two."))),
                DescribeRole.Theorem))));
}
