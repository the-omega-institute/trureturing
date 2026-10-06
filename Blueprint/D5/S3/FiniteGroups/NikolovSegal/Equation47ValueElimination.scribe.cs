using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ValueEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Value elimination and reconstruction.",
        H("Value elimination and reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valueelimination-normalized-value-forest-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueElimination.normalized_value_forest_reconstruction"),
                H("normalized value forest reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the genuine value leaf order, solving one residual equation at every powered-component root reconstructs all normalized vertex targets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valueelimination-corrected-value-forest-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueElimination.corrected_value_forest_reconstruction"),
                H("corrected value forest reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reconstructed normalized values give genuine corrected q-powered factor tuples with all prescribed cycle-base scalars."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
