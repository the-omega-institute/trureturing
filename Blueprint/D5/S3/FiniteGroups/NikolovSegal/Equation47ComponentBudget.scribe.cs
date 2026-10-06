using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ComponentBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Component movement and residual support budgets.",
        H("Component movement and residual support budgets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47componentbudget-component-movement-value-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ComponentBudget.component_movement_value_bound"),
                H("component movement value bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The movement sum on one actual powered component is at most twice its number of genuine nonbase value coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47componentbudget-normalized-component-typeii-residual-budget"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ComponentBudget.normalized_component_typeII_residual_budget"),
                H("normalized component typeII residual budget"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a component of n at least two vertices, movement at least (4+2D)n leaves residual support of at least n+2D+1 after its n minus one forest links."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
