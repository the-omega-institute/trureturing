using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TransverseMetric;

internal sealed class NativePositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native transverse positivity and the negative right-C0 pairing",
        H("Native transverse positivity and the negative right-C0 pairing"),
        Blocks(
            Paragraph(Text("The transverse axis type is exactly the subtype of Fin D.rank excluding xAxis and yAxis. Its Gram is the real part of the actual gramPair of the corresponding frame rows. Star-fixed transverse rows make the full Gram real and identify it with the real row Gram used by the actual pullback theorem. nativePolynomial is literally coordinateSub composed with the injective transverse variable renaming, hence contains no longitudinal occupation. The original nativeTransverseEnergySpace span is reused with both Gram inverse and both frame inverse equations. On its genuine two ghost partners, J has eigenvalues one and two; the exact operator 2 id - J kills the epsilon partner and retains literal down states. No physical quotient, cohomology descent or HPL isometry is used. The original Hplus and actual right C D 0 normalization give raw F(u,C0 u) = -fockForm(p,p), so the positive statement has the fixed minus sign. Charges and integer levels are arbitrary; empty transverse dimensions and negative levels are not excluded. The full string and AdS/CFT objective remains open.")),
            Describe.Lean(
                DescribeId.Create("nativepositivity-transverseaxis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.TransverseAxis"),
                H("True finite transverse axes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-transverseindex"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.transverseIndex"),
                H("Original oscillator index embedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-transverserows"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.transverseRows"),
                H("Real parts of the actual transverse rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-transversegram"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.transverseGram"),
                H("Actual transverse Gram matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-nativepolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.nativePolynomial"),
                H("Original native transverse polynomial image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-nativedown"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.nativeDown"),
                H("Literal original tensor down states"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativepositivity-transversegram-actual-real"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.transverseGram_actual_real"),
                H("Reality of the full actual transverse Gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativepositivity-nativepolynomial-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.nativePolynomial_positive"),
                H("Strict native transverse matter positivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativepositivity-nativepolynomial-norm-real"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.nativePolynomial_norm_real"),
                H("Real native transverse matter norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativepositivity-nativepolynomial-injective"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.nativePolynomial_injective"),
                H("Faithfulness of the native polynomial image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativepositivity-native-j-one-down"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.native_J_one_down"),
                H("Exact native degree-one down representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativepositivity-native-degree-one-negative-c0-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/NativePositivity.native_degree_one_negative_C0_positive"),
                H("Strict positive real negative right-C0 pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact statement is supplied by the compiled source. This describes original-carrier mathematics only; source audit enrollment and evaluator acceptance are separate obligations."))),
                DescribeRole.Theorem))));
}
