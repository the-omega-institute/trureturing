using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIISLnF2WholeUDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn F2 Whole U.",
        H("Type-A SLn F2 Whole U"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2wholeu-identity-pivots-inner-on-u"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU.identity_pivots_inner_on_U"),
                H("identity pivots inner on U"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A normalized bare automorphism with identity simple pivots agrees with one actual U-inner automorphism on the WHOLE U."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2wholeu-positivegraph-twice-u"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU.positiveGraph_twice_U"),
                H("positiveGraph twice U"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual graph convention is involutive on U by its genuine simple-root law and the generation proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2wholeu-positivegraph-map-uplus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU.positiveGraph_map_Uplus"),
                H("positiveGraph map Uplus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual graph U stability, proved using literal simple roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2wholeu-normalized-whole-u-inner-graph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU.normalized_whole_U_inner_graph"),
                H("normalized whole U inner graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuinely missing F2 whole-U agreement: a bare U-normalized full-group automorphism has only inner and positive-graph action on U. The pivot permutation and simultaneous conjugator are DERIVED."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
