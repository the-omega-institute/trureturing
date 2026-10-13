using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnClassWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Class Width.",
        H("Type-A SLn Class Width"),
        Blocks(
            Paragraph(Text("Constructive uniform class product width for the actual fixed long-cycle qth power. The elementary12-word is consumed on6480 genuine small supported upper factors, then the accepted25 upper/lower width. Original PartII Section5 uses LS2; this module proves the needed type-A large-rank width directly. No class-product coverage or width oracle is a premise.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnclasswidth-actual-fixed-cycle-upper-full-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnClassWidth.actual_fixed_cycle_upper_full_class_word"),
                H("actual fixed cycle upper full class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every upper target, over every field, is an exact77760-word in the SAME fixed q-power class. All6480 support slots (including identities) are constructed from the actual80 consecutive coordinate chunks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnclasswidth-actual-fixed-cycle-lower-full-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnClassWidth.actual_fixed_cycle_lower_full_class_word"),
                H("actual fixed cycle lower full class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lower targets use the genuine inverse-transpose automorphism, which FIXES the constructed permutation matrix. The conjugacy class is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnclasswidth-actual-fixed-cycle-full-group-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnClassWidth.actual_fixed_cycle_full_group_class_word"),
                H("actual fixed cycle full group class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full actual SLn class coverage at one absolute positive length1944000, independent of field, rank, q and target. No finite-field assumption. The same fixed matrix supplies all25 genuine alternating unipotent slots."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
