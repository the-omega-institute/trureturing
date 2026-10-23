using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIIFixedSLnPowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Fixed SLn Power.",
        H("Type-A Fixed SLn Power"),
        Blocks(
            Paragraph(Text("PartII Section5, printed pp249--251: actual type-A fixed qth powers. The paper cites [SW] for Lemma5.1. Here the stated type-A power-form class estimate is proved independently by explicit reflected permutation matrices, exact centralizer row coordinates, the Uplus chart and an injective UL big cell. No SW/LS2/class-width/CFSG input is assumed. The original finite-outer value construction is consumed with original q/e powers and one correction before all witnesses. Full class-width and all-simple uniform scalar product remain unproved.")),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-fixedelement"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.fixedElement"),
                H("fixedElement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A characteristic-independent, actual determinant-one permutation matrix in the D0PhiGamma fixed subgroup. Its two reflected cycles have length q+1, fix both boundary coordinates, and preserve height parity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-fixed-element"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_element"),
                H("actual fixed element"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual full boundary-diagonal, field and positive-graph actions fix the constructed matrix. No fixed-element law is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-fixed-power-nonidentity"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_nonidentity"),
                H("actual fixed power nonidentity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Its qth power is nonidentity for EVERY positive q, independently of characteristic. This does not assert the still-missing large-class bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-fixed-power-noncentral"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_noncentral"),
                H("actual fixed power noncentral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The qth power is genuinely noncentral, not merely nonidentity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-small-field-fixed-power-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_fixed_power_values"),
                H("actual small field fixed power values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual original selected Fin/q-over-e value construction in the small-field branch, now with a constructed fixed element and noncentral qth power. The rank-independent finite-outer bound and one correction are genuine. This is value range, not the unproved uniform class width."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-fixed-centralizer-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_centralizer_card"),
                H("actual fixed centralizer card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual centralizer coordinates: every row of a commuting matrix is reconstructed from the two long-cycle base rows and untouched rows. This derives an injection; no centralizer-size estimate is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-q-power-centralizer-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_centralizer_card"),
                H("actual q power centralizer card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coprimality is implemented by (z^q)^r=z^-1 for a cycle of length qr+1. Thus the ACTUAL qth-power centralizer has the same row bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-q-power-class-lower"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_class_lower"),
                H("actual q power class lower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quantitative actual conjugacy class of the fixed qth power. The centralizer rows and genuine UL big-cell lower bound give this estimate; no SW/LS2 power-class or class-width theorem is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-q-power-large-class"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_large_class"),
                H("actual q power large class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An elementary type-A Lemma5.1 bound in power form: when qr>=k+2, |SLn(F)|<=|class(z^q)|^8, with z fixed by the constructed D0PhiGamma. The class-width theorem is a separate, still-unproved obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-small-field-large-class-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_large_class_values"),
                H("actual small field large class values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Section5's actual long-cycle value consumer, with the quantitative class estimate conjoined and the fixed-element law proved. R remains the number of desired ordinary valueS; uniform class width is not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedslnpower-actual-all-large-rank-fixed-power"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_all_large_rank_fixed_power"),
                H("actual all large rank fixed power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All sufficiently large actual ranks, with no rank congruence premise. The Euclidean decomposition constructs the two long cycles; z and its large qth-power class are chosen before EVERY boundary DFG action."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
