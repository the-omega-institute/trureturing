using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIIPSLnF2BareFullGroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn F2 Bare Full Group.",
        H("Type-A PSLn F2 Bare Full Group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiipslnf2barefullgroup-psl-bare-full-group-inner-graph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2BareFullGroup.psl_bare_full_group_inner_graph"),
                H("psl bare full group inner graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic bare PSLn over EVERY two-element field, EVERY n>=5. The actual quotient isomorphism is proved in the F2 residual input, not assumed as an automorphism-lift premise. One actual projective inner correction and graph choice precede EVERY SL representative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnf2barefullgroup-psl-bare-full-group-inner-graph-aut"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2BareFullGroup.psl_bare_full_group_inner_graph_aut"),
                H("psl bare full group inner graph aut"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal equality on all quotient targets with the induced central quotient action, without an alpha-lift assumption."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
