using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2RootNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2RootNormalization.",
        H("Part II SL2RootNormalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-root-inverse-addequiv-ring"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.root_inverse_addEquiv_ring"),
                H("root inverse addEquiv ring"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every finite field, an additive equivalence fixing one and preserving inversion is a ring automorphism. Hua identities yield multiplication in characteristic different from two; the finite-field square map resolves characteristic two. No lower bound on field size is imposed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-a1weyl-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_product"),
                H("a1Weyl product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any field and nonzero x, the ordered upper(x), lower(-inverse(x)), upper(x) product equals the explicit determinant-one Weyl matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-a1weyl-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_upper"),
                H("a1Weyl upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by the explicit Weyl matrix takes upper(t) to lower(-(inverse(x))^2 t) for nonzero x over any field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-actual-root-pair-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_pair_SL2_scalar_product"),
                H("actual root pair SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Additive coordinate equivalences for the two actual SL2 roots determine field actions by Weyl and Hua relations in both characteristics. This constructs the scalar PRODUCT from the stated genuine root laws, under the field and length bounds, without a semilinearity premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-actual-root-coordinate-equiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_coordinate_equiv"),
                H("actual root coordinate equiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an injective additive root parametrization in any group, an automorphism preserving its actual range induces an additive equivalence on the field coordinates. Range equality provides the inverse map; the root multiplication law gives additivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootnormalization-actual-root-stabilizing-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_stabilizing_SL2_scalar_product"),
                H("actual root stabilizing SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Automorphisms preserving the actual upper and lower SL2 root ranges satisfy the scalar PRODUCT under the quantitative bounds. Additive root coordinates and their field action are constructed, rather than supplied as assumptions."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
