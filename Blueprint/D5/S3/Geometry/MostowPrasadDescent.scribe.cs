using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MostowPrasadDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MostowPrasadDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate isometric actions descend to an equivalence of orbit quotients.",
        H("Mostow--Prasad descent through orbit quotients"),
        Blocks(
            Paragraph(Text(
                "This module supplies the quotient-side bridge for holonomy rigidity. "
                    + "It is independent of the hyperbolic lattice theorem: once a group "
                    + "isomorphism is implemented by a chosen ambient isometry, that isometry "
                    + "descends to the corresponding orbit quotients.")),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-orbit-setoid"),
                DeclarationHandle.Create(Prefix + "orbitSetoid"),
                H("Orbit relation of an isometric representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "orbitSetoid identifies points related by one element of the represented "
                        + "group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-orbit-quotient"),
                DeclarationHandle.Create(Prefix + "OrbitQuotient"),
                H("Orbit quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "OrbitQuotient is the set-theoretic quotient by the representation orbit "
                        + "relation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-orbit-quotient-mk"),
                DeclarationHandle.Create(Prefix + "orbitQuotientMk_eq_of_orbit"),
                H("Orbit-related points have equal quotient classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical projection identifies any two points related by the "
                        + "represented group."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-isometric-conjugacy"),
                DeclarationHandle.Create(Prefix + "IsometricGroupConjugacy"),
                H("Isometric group conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A group isomorphism is implemented by a chosen isometry conjugating the "
                        + "two representations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-map"),
                DeclarationHandle.Create(Prefix + "descendedMap"),
                H("Descended quotient map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The chosen conjugator gives a well-defined map from the first orbit "
                        + "quotient to the second."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-inverse"),
                DeclarationHandle.Create(Prefix + "descendedInverse"),
                H("Descended inverse map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse conjugator gives the reverse quotient map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-equivalence"),
                DeclarationHandle.Create(Prefix + "descendedEquiv"),
                H("Equivalence of orbit quotients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The descended map and its inverse form an equivalence of the two orbit "
                        + "quotients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-map-commutes"),
                DeclarationHandle.Create(Prefix + "descendedMap_comp_orbitQuotientMk"),
                H("The descended map commutes with the quotient projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On every representative point, the quotient map is exactly induced by "
                        + "the ambient conjugator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-descent-equivalence-commutes"),
                DeclarationHandle.Create(Prefix + "descendedEquiv_comp_orbitQuotientMk"),
                H("The quotient equivalence commutes with the projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence has the expected representative-level formula."))),
                DescribeRole.Theorem)),
        []));
}
