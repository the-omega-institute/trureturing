using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed norms and power-family point evaluations.",
        H("Defs"), Blocks(
            Describe.Lean(DescribeId.Create("dm-defs-circlemean"),
                DeclarationHandle.Create("D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.circleMean"),
                H("Circle integral means"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/dmitrovic2024norm")),
                Blocks(Paragraph(Text("For finite positive p the angular p-th powers are averaged over one full period and the p-th root is taken. At infinity the mean is the angular supremum."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dm-defs-mixednorm"),
                DeclarationHandle.Create("D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.mixedNorm"),
                H("Weighted radial mixed norms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/dmitrovic2024norm")),
                Blocks(Paragraph(Text("For finite positive q the q-th power integral uses density 2 alpha q r (1-r squared) raised to alpha q minus one. At infinity the norm is the supremum of the weighted angular means on radii strictly between zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dm-defs-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim"),
                H("The constant-one point evaluation conjecture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/dmitrovic2024norm")),
                Blocks(Paragraph(Text("The cited article defines the mixed norm on p. 697 and conjectures this estimate on p. 705. The parameters p and q range over positive extended nonnegative reals and alpha is positive. The function is holomorphic on the open unit disc and has finite mixed norm. The evaluation inequality is multiplied by the positive boundary weight. At p=infinity the reciprocal of p.toReal is zero."))),
                DescribeRole.Definition))));
}
