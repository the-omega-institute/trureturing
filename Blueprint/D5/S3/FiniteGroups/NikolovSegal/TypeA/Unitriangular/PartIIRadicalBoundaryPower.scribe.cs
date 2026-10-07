using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIRadicalBoundaryPowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Radical Boundary Power.",
        H("Type-A Radical Boundary Power"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-pair-square"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_pair_square"),
                H("actual pair square"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual exceptional pair square: coefficients of the two opposite roots remain distinct. The diagonal determinant obstacle has not been erased or declared an inverse transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-even-pair-power"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_even_pair_power"),
                H("actual even pair power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual even power, with distinct nonzero exceptional scalars; this is the concrete coefficient normalization needed before Lemma7.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-boundary-norm-value"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_boundary_norm_value"),
                H("actual boundary norm value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual original-d-power boundary value, with its genuinely distinct scalar coefficients. These depend on the prescribed action BEFORE any target; the commutator witness itself carries the target parameters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-boundary-torus-orbit-factors"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_boundary_torus_orbit_factors"),
                H("actual boundary torus orbit factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact lambda normalization for the actual exceptional scalar tuple. The residual mu is fixed by a/phi/eps/d, BEFORE every target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-boundary-scalar-nonzero"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_boundary_scalar_nonzero"),
                H("actual boundary scalar nonzero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pre-target scalar tuple really is nonzero: it is a product of actual diagonal-unit weights and their genuine field images."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-boundary-inner-torus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_boundary_inner_torus"),
                H("actual boundary inner torus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Concrete determinant-one torus correction, before target witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-boundary-norm-field-value"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_boundary_norm_field_value"),
                H("actual boundary norm field value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual normalized fieldValue, consuming the original-power norm witness and the exact lambda orbit factor. This closes coefficient normalization; full boundary support/product assembly remains separate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalboundarypower-actual-inner-radical-axis-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower.actual_inner_radical_axis_product"),
                H("actual inner radical axis product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine bounded-length boundary-axis product in V modulo its corner: every off-axis coordinate is proved zero. The same actual INNER tuple precedes all scalar targets. No coverage premise remains."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
