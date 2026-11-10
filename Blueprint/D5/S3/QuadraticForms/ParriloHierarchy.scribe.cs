using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class ParriloHierarchyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/ParriloHierarchy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full copositive polynomial SOS hierarchy",
        H("The full copositive polynomial SOS hierarchy"), Blocks(
            Paragraph(Text("For every level k, K consists of real symmetric M for which (sum_i X_i squared)^k times sum_ij M_ij X_i squared X_j squared is a native real sum of squares. The definitions use the genuine squared-variable substitution and cover every finite dimension, with no normalization. This is the hierarchy used by Gulati-Nechita-Park. The separate BoseHierarchy module proves its actual tensor-extension characterization.")),
            Describe.Lean(DescribeId.Create("parrilo-lifted-form"),
                DeclarationHandle.Create(Prefix + "liftedForm"),
                H("Homogeneous form before squaring variables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree is k+2. All ordered matrix entries contribute, so off-diagonal entries occur twice for symmetric matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parrilo-polynomial"),
                DeclarationHandle.Create(Prefix + "polynomial"),
                H("Actual Parrilo polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native expand map substitutes X_i squared in the homogeneous form, yielding exactly the standard level-k polynomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parrilo-k"),
                DeclarationHandle.Create(Prefix + "K"),
                H("Full native SOS hierarchy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predicate is real symmetry and unrestricted native IsSumSq of the actual polynomial. Zero and singular matrices are retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parrilo-closed"),
                DeclarationHandle.Create(Prefix + "K_closed"),
                H("Closedness at every level"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real linear coefficient map of the degree-2(k+2) polynomial pulls back the closed native homogeneous SOS cone. Intersecting with real symmetric matrices proves closedness of every actual level."))), DescribeRole.Theorem))));
}
