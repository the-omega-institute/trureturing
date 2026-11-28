using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.CosetActions;

internal sealed class TransitiveEtaleActionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/CosetActions/TransitiveEtaleAction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar invariants force a finite étale action to be a coset permutation action.",
        H("Transitive actions on finite étale complex algebras"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transitive-etale-coset-algebra"),
                DeclarationHandle.Create(Module + ".exists_coset_algEquiv"),
                H("Scalar invariants give a coset function algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group G act by complex algebra automorphisms on a nontrivial "
                        + "finite étale commutative complex algebra A. Assume every element fixed by all of G "
                        + "is a scalar multiple of the unit. Then for some subgroup K of G there is a complex "
                        + "algebra isomorphism from A to the algebra of all complex-valued functions on the "
                        + "left cosets G/K. Under this isomorphism, g acts by pulling back along left "
                        + "multiplication by the inverse of g.")),
                    Paragraph(Text("Evaluation identifies A with the functions on its nonempty set of complex "
                        + "points. The point action is precomposition by the inverse automorphism. The "
                        + "indicator of the orbit of a chosen point is invariant, so its preimage in A is "
                        + "scalar. The indicator is therefore constant, and its value at the chosen point "
                        + "is one, so the orbit contains every point. Take K to be the stabilizer of that "
                        + "point and reindex evaluation along the equivariant bijection from G/K to the orbit."))),
                DescribeRole.Theorem),
            Paragraph(Text("See Davydov and Simmons, On Lagrangian algebras in group-theoretical braided fusion "
                + "categories, Lemma 2.10. https://arxiv.org/abs/1603.04650")))));
}
