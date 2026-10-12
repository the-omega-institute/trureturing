using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnTorusAlignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Torus Alignment.",
        H("Type-A SLn Torus Alignment"),
        Blocks(
            Paragraph(Text("Actual all-rank diagonal-torus alignment. The weighted matrix average generalizes the PartIIA2TorusAlignment (rank3) proof, without a complement-conjugacy or classification assumption.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislntorusalignment-upper-finite-subgroup-diagonal-alignment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.upper_finite_subgroup_diagonal_alignment"),
                H("upper finite subgroup diagonal alignment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One actual Uplus element simultaneously aligns a whole finite triangular subgroup whenever its genuine order is invertible in the field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislntorusalignment-torusdiagonalunits"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.torusDiagonalUnits"),
                H("torusDiagonalUnits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine diagonal-entry embedding of the literal SL torus into units."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislntorusalignment-card-torus-dvd-units"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.card_torus_dvd_units"),
                H("card torus dvd units"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No order oracle: Lagrange applied to the actual unit-entry embedding."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislntorusalignment-u-preserving-torus-alignment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.U_preserving_torus_alignment"),
                H("U preserving torus alignment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Further correction of an actual U-preserving automorphism by an actual Uplus element. Its torus-image order and triangularity are derived."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislntorusalignment-sl-inner-u-t-correction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.sl_inner_U_T_correction"),
                H("sl inner U T correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One actual determinant-one inner correction, before all targets, preserves full Uplus and the literal diagonal torus in every rank."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
