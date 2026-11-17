using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class HomogeneousSOSGramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/HomogeneousSOSGram.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Gram matrices and closed homogeneous SOS cones",
        H("Positive Gram matrices and closed homogeneous SOS cones"), Blocks(
            Paragraph(Text("The polynomial cone uses the native unrestricted real sum-of-squares predicate. Homogeneous square extraction and genuine PSD Gram factorization supply its finite representation. These results supply polynomial prerequisites for GNP; the tensor-extension characterization is a separate obligation.")),
            Describe.Lean(DescribeId.Create("sosgram-exponent"),
                DeclarationHandle.Create(Prefix + "Exponent"),
                H("Fixed-degree monomials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All finitely supported nonnegative integer exponents with the prescribed total degree are retained, including degree zero and the empty variable type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sosgram-form"),
                DeclarationHandle.Create(Prefix + "form"),
                H("Actual homogeneous coefficient form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient vector is expanded in the ordinary monomials, without multinomial weights or normalization factors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sosgram-gram"),
                DeclarationHandle.Create(Prefix + "gram"),
                H("Actual Gram polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix entry indexed by exponents a,b multiplies the monomial with exponent a+b. Positivity is ordinary real matrix positive semidefiniteness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sosgram-iff"),
                DeclarationHandle.Create(Prefix + "homogeneous_sos_iff_gram"),
                H("Native SOS iff positive Gram representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every homogeneous real form of degree twice d is a native sum of squares exactly when it is the actual Gram polynomial of a PSD real matrix on all degree-d monomials. The forward direction uses homogeneous square representatives; the converse factors the PSD matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sosgram-map"),
                DeclarationHandle.Create(Prefix + "gramMap"),
                H("Gram coefficient map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This real linear map extracts the actual degree-2d coefficients of the Gram polynomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sosgram-cone"),
                DeclarationHandle.Create(Prefix + "sosCoefficients"),
                H("Native homogeneous SOS coefficient cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership means that the corresponding actual homogeneous polynomial is a native sum of squares; it is not defined as a closure or a relaxed cone."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sosgram-closed"),
                DeclarationHandle.Create(Prefix + "sosCoefficients_closed"),
                H("Closedness of the native homogeneous SOS cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A zero Gram polynomial with PSD Gram matrix forces every square representative, hence the matrix, to vanish. Compactness of the cone's unit slice then bounds lifts under the coefficient projection and proves its image closed. This closedness does not remove the closure from the ordinary DPS polar-sum identity."))), DescribeRole.Theorem))));
}
