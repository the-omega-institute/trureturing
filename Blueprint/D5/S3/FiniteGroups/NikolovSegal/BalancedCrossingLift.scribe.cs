using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class BalancedCrossingLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal crossings before reduction.",
        H("Literal crossings before reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-balancedcrossinglift-balanced-nontrivial-crossing"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BalancedCrossingLift.balanced_nontrivial_crossing"),
                H("balanced nontrivial crossing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A balanced word with nontrivial free-group reduction has an actual literal crossing; the reduction crossing lifts to a sublist of the original word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-balancedcrossinglift-crossing-balanced"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BalancedCrossingLift.crossing_balanced"),
                H("crossing balanced"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ADCBE crossing surgery preserves balance of every remaining key."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-balancedcrossinglift-crossing-support-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BalancedCrossingLift.crossing_support_card"),
                H("crossing support card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Deleting the crossing keys lowers support by exactly two."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
