using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous sign matrix bounds give indecomposable k-entanglement-breaking maps.",
        H("Indecomposable maps from finite Hermitian signs"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixconstruction-finitesignsample-unconditional"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.finiteSignSample_unconditional"),
                H("Simultaneous bounds in the sign cube"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each of the three bad events has probability less than one quarter under the same uniform measure. One assignment lies outside their union. The norm bounds give positive semidefiniteness for both trace tests, and the Schmidt bound gives separability after local congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixconstruction-exists-indecomposable-keb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_indecomposable_kEB"),
                H("Indecomposable k-entanglement-breaking maps"), StatementSource.FromAuthor(F.Disp(Family())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each natural number k at least two and every natural number d at least 524288 times k cubed, there is a complex-linear k-entanglement-breaking map from the full d by d matrix algebra into itself that is indecomposable."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixconstruction-exists-signcubesample-good"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_signCubeSample_good"),
                H("Exists sign cube sample good"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For k at least two and dimension at least 524288 times k cubed, a single assignment has the Schmidt-restricted quadratic bound and operator norms at most four times d for both the matrix and its output partial transpose."))),
                DescribeRole.Theorem))));

    private static Formula Family()
    {
        Formula k = F.Id("k"), d = F.Id("d"), map = F.Id("f");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula cutoff = new Formula.Binary(F.D(5, 2, 4, 2, 8, 8), FormulaBinaryOperator.Multiply,
            new Formula.Power(k, F.D(3)));
        Formula condition = new Formula.Logic(
            new Formula.Relation(F.D(2), FormulaRelationOperator.LessThanOrEqual, k),
            FormulaLogicOperator.And,
            new Formula.Relation(cutoff, FormulaRelationOperator.LessThanOrEqual, d));
        Formula properties = new Formula.Logic(
            new Formula.FunctionCall(FormulaIdentifier.Create("IsKEB"), [k, map]),
            FormulaLogicOperator.And,
            new Formula.Not(new Formula.FunctionCall(FormulaIdentifier.Create("IsDecomposable"), [map])));
        Formula exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("f"),
            new Formula.FunctionCall(FormulaIdentifier.Create("MatrixMap"), [d, d]), properties);
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"), naturals,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"), naturals,
                new Formula.Logic(condition, FormulaLogicOperator.Implies, exists)));
    }
}
