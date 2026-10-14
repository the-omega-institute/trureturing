using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TransverseMetric;

internal sealed class FiniteRowFockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real row positivity of the actual Fock form",
        H("Finite real row positivity of the actual Fock form"),
        Blocks(
            Paragraph(Text("The original matter oscillator polynomial algebra and its original fockForm are unchanged. A finite family of real creation rows has the actual restricted Gram rows * gramReal D * rows.transpose. Pullback is proved using the original creation-annihilation adjoint and polynomial derivative recursion. The diagonal auxiliary coefficient expression is not an assumed replacement metric: its agreement with the actual pairing is proved. Restricted-Gram LDL gives strictly positive factorial and frequency occupation weights. An inverse coordinate substitution proves that every nonzero polynomial has a nonzero transformed coefficient. Ambient positivity, integrality of the restricted Gram, orthonormal rows, dimension restrictions and energy cutoffs are absent. This extends existing Fock coefficient mathematics to rectangular finite creation maps; it makes no literature novelty claim.")),
            Describe.Lean(
                DescribeId.Create("finiterowfock-occupationweight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.occupationWeight"),
                H("Factorial and positive-frequency occupation weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowpolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowPolynomial"),
                H("Actual real row creation map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowgram"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowGram"),
                H("Actual restricted row Gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finiterowfock-changecoordinates"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.changeCoordinates"),
                H("Finite coordinate substitution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowpolynomial-norm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowPolynomial_norm"),
                H("Actual pullback coefficient formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowpolynomial-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowPolynomial_positive"),
                H("Strict positivity under restricted Gram positivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowpolynomial-injective"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowPolynomial_injective"),
                H("Faithful polynomial embedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiterowfock-rowpolynomial-norm-real"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock.rowPolynomial_norm_real"),
                H("Reality of the actual norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem))));
}
