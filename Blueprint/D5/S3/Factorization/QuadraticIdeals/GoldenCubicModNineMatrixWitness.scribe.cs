using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicModNineMatrixWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cayley-Hamilton sixth power detects a nontrivial mod-nine congruence direction.",
        H("Cayley-Hamilton gives the exact universal sixth power"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-mod9-sixth-formula"),
                DeclarationHandle.Create(Module + "sixth_formula"),
                H("Cayley-Hamilton gives the exact universal sixth power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For determinant one and trace four or five, the Cayley-Hamilton cubic collapses to an affine expression modulo nine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-sixth-not-identity"),
                DeclarationHandle.Create(Module + "sixth_not_identity"),
                H("The sixth power is nontrivial modulo nine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If it were trivial, the entry constraints would force the characteristic discriminant to be zero modulo nine, contradicting either trace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-sixth-reduces-to-identity"),
                DeclarationHandle.Create(Module + "sixth_reduces_to_identity"),
                H("The sixth power reduces to identity modulo three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit scalar coefficients vanish or become one in the residue field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-companion-four-sixth"),
                DeclarationHandle.Create(Module + "companion_four_sixth"),
                H("The trace-four companion sixth power is explicit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-by-two identity holds over the ring modulo nine, not only in the residue field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-companion-five-sixth"),
                DeclarationHandle.Create(Module + "companion_five_sixth"),
                H("The trace-five companion sixth power is explicit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second trace case has its own exact companion certificate."))),
                DescribeRole.Theorem))));
}
