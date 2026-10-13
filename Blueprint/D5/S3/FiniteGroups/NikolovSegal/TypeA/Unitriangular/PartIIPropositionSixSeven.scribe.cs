using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIPropositionSixSevenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Proposition Six Seven.",
        H("Type-A Proposition Six Seven"),
        Blocks(
            Paragraph(Text("Actual untwisted Proposition6.7, PartII pp262–263. Six genuine value batches retain the extra corner; no printed corner omission is assumed.")),
            Describe.Lean(
                DescribeId.Create("typea-partiipropositionsixseven-actual-six-batch-radical-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixSeven.actual_six_batch_radical_product"),
                H("actual six batch radical product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full actual radical value reconstruction. All six diagonal INNER correction tuples precede every nonlinear radical target. Original positive divisor powers and the exact noncommutative product are kept."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipropositionsixseven-actual-proposition6-7-uniform-inner-v-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixSeven.actual_proposition6_7_uniform_inner_V_product"),
                H("actual proposition6 7 uniform inner V product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quantitative actual untwisted Proposition6.7, with a rigorously proved chosen length 6*(2q(2q+1)+1), including the full corner. N,C are chosen before all finite fields, ranks and prescribed tuples. Every correction is an actual diagonal SL INNER correction, before all targets."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
