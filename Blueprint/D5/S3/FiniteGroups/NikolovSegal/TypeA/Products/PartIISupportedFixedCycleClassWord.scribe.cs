using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISupportedFixedCycleClassWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Supported Fixed Cycle Class Word.",
        H("Type-A Supported Fixed Cycle Class Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedfixedcycleclassword-actual-cycle-block-conjugate-supported"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord.actual_cycle_block_conjugate_supported"),
                H("actual cycle block conjugate supported"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extract and transport the literal upper supported block to the genuine fixed-cycle block. The auxiliary double block is identity, not u^-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedfixedcycleclassword-actual-fixed-cycle-ordered-supported-upper-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord.actual_fixed_cycle_ordered_supported_upper_class_word"),
                H("actual fixed cycle ordered supported upper class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EVERY actual upper-unitriangular supported matrix on ANY d ordered coordinates is a literal ordered12-word in the SAME fixedElement^q class. No extraction, permutation, determinant-one transport or class-width oracle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedfixedcycleclassword-actual-fixed-cycle-finset-supported-upper-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord.actual_fixed_cycle_finset_supported_upper_class_word"),
                H("actual fixed cycle finset supported upper class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary finite support of cardinality AT MOST d. ordered enumeration uses its actual cardinality; the fixed class and12 slots remain exactly unchanged, including empty support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedfixedcycleclassword-actual-fixed-cycle-set-supported-upper-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord.actual_fixed_cycle_set_supported_upper_class_word"),
                H("actual fixed cycle set supported upper class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal Set support version; finiteness is intrinsic to the ambient finite coordinate type, and NO finite-field hypothesis is required."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
