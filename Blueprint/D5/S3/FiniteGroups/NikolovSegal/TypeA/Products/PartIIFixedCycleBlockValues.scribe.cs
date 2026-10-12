using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIIFixedCycleBlockValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Fixed Cycle Block Values.",
        H("Type-A Fixed Cycle Block Values"),
        Blocks(
            Paragraph(Text("Even powers on the actual q-powered long cycle give a coordinate injection with image disjoint from the next odd powers, using coprimality of qr+1 and q. The prescribed bare PSLn/divisor tuple consumes the resulting class word with its correction fixed before all block targets. This local shifted range is consumed in the complete product assembly.")),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedcycleblockvalues-actualcycleembedding"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues.actualCycleEmbedding"),
                H("actualCycleEmbedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual 2d-coordinate block sits on even powers in one selected long cycle of the constructed fixed matrix. No abstract cycle law is input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedcycleblockvalues-actual-fixed-cycle-upper-class-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues.actual_fixed_cycle_upper_class_word"),
                H("actual fixed cycle upper class word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine TWELVE-factor class-word reconstruction on the concrete long-cycle block, with no displacement/cycle/class-width hypothesis left."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiifixedcycleblockvalues-actual-bare-psln-fixed-cycle-block-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues.actual_bare_PSLn_fixed_cycle_block_values"),
                H("actual bare PSLn fixed cycle block values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original arbitrary bare projective actions and q/e, with one global correction before every genuine block target. The exact shifted target is retained; full-group/uniform class width is not assumed or asserted."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
