using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MostowPrasadRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MostowPrasadRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metric and group-conjugacy interfaces for the Mostow--Prasad rigidity endpoint.",
        H("Mostow--Prasad rigidity: metric and group interfaces"),
        Blocks(
            Paragraph(Text(
                "The reusable interfaces for the Mostow--Prasad endpoint include metric uniqueness "
                    + "and the algebraic statement that holonomy representations are related by "
                    + "conjugacy in an ambient group. The full theorem requires additional "
                    + "hyperbolic geometry and is not claimed by this module.")),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-uniqueness"),
                DeclarationHandle.Create(Prefix + "isometry_equiv_eq_of_eqOn_dense"),
                H("Dense-set uniqueness of isometries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two isometry equivalences that agree on a dense subset of the source "
                        + "are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-range-uniqueness"),
                DeclarationHandle.Create(Prefix + "isometry_equiv_eq_of_dense_range"),
                H("Dense-range uniqueness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same uniqueness result accepts a dense parametrization directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-has-isometry-representative"),
                DeclarationHandle.Create(Prefix + "HasIsometryRepresentative"),
                H("Existence of an isometry representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A homotopy equivalence has an isometry representative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-unique-isometry-representative"),
                DeclarationHandle.Create(Prefix + "UniqueIsometryRepresentative"),
                H("Uniqueness of an isometry representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All isometry representatives in one homotopy class are equal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-endpoint"),
                DeclarationHandle.Create(Prefix + "MostowPrasadRigidityEndpoint"),
                H("Mostow--Prasad endpoint specification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every homotopy equivalence has a unique isometry representative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-isometry-representative-of-isometry"),
                DeclarationHandle.Create(Prefix + "hasIsometryRepresentative_of_isometry"),
                H("An isometry supplies its representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An isometry induces a homotopy equivalence for which it is a representative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-unique-representative-dense"),
                DeclarationHandle.Create(Prefix + "uniqueIsometryRepresentative_of_eqOn_dense"),
                H("Dense boundary criterion for uniqueness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Agreement on a dense boundary set proves uniqueness of representatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-endpoint-from-parts"),
                DeclarationHandle.Create(Prefix + "existsUnique_isometryRepresentative_of_parts"),
                H("Endpoint from existence and uniqueness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existence and uniqueness obligations combine into the exact endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy"),
                DeclarationHandle.Create(Prefix + "GroupConjugacy"),
                H("Group conjugacy interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An abstract group isomorphism is realized by conjugacy in an ambient group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy-symm"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_symm"),
                H("Symmetry of group conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The group-conjugacy relation is preserved by inverting the group isomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy-trans"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_trans"),
                H("Composition of group conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugacy certificates compose along group isomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugator-unique"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_conjugator_unique"),
                H("Uniqueness of the conjugator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A trivial centralizer for the holonomy image makes the ambient conjugator unique."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-orbit"),
                DeclarationHandle.Create(Prefix + "DenseOrbit"),
                H("Dense holonomy orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The orbit of a chosen basepoint under an isometry representation is dense."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-orbit-centralizer"),
                DeclarationHandle.Create(Prefix + "rangeCentralizerTrivial_of_dense_orbit"),
                H("Dense orbit centralizer criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A dense orbit and basepoint control imply a trivial centralizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-attracting-poles-centralizer"),
                DeclarationHandle.Create(Prefix + "rangeCentralizerTrivial_of_dense_attracting_poles"),
                H("Dense attracting poles force a trivial centralizer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be any group, X any Hausdorff topological space in which every "
                            + "pair of points has a third point distinct from both, and rho a group "
                            + "homomorphism from G to the homeomorphisms of X. Suppose the set of "
                            + "a for which there are g in G and b in X with a distinct from b, "
                            + "such that the n-fold iterate of rho(g) at every x distinct from b "
                            + "converges to a, is dense in X. Then every homeomorphism commuting "
                            + "with every rho(g) is the identity.")),
                    Paragraph(Text(
                        "For each attracting pole a, choose x away from b and the inverse image "
                            + "of b under a centralizing homeomorphism z. Commutation transports "
                            + "the entire iterated orbit through z. Continuity makes its limit z(a), "
                            + "while the attracting-pole condition makes the same orbit converge to "
                            + "a. Hausdorff uniqueness fixes a; density and continuity fix all of X.")),
                    Paragraph(Text(
                        "This gives a conditional route to the centralizer premise of "
                            + "groupConjugacy_conjugator_unique. It does not construct an ideal "
                            + "boundary, establish north-south dynamics or lattice pole density, "
                            + "prove faithfulness, construct a conjugator, or prove "
                            + "MostowPrasadRigidityEndpoint."))),
                DescribeRole.Theorem)),
        []));
}
