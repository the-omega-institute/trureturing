using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportQuadraticTowerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportQuadraticTower." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quadratic tower and independent-parameter quartic", H("Actual quadratic tower and independent-parameter quartic"),
        Blocks(
            Paragraph(Text("Let k be a characteristic-zero field and let K=k(b). The quadratic field H=K(sqrt(D)) and the further quadratic field F=H(sqrt(f)) use the fixed polynomials of the six-support equality curve. The finite places considered here lie above roots of D on the affine b-line. Their normalized multiplicative valuations, residue fields and ramification indices refer to the actual integral closure and its prime localizations.")),
            Item("field-degree", "degree_F", "Actual degree-four field extension", "The tower K=k(b), H=K(sqrt D), F=H(sqrt f) has exact degrees2,2,4 over every characteristic-zero field. The two quadratic steps are certified by nonsquare norms."),
            Item("geometric", "actual_geometric_irreducibility", "Full coefficient-extension irreducibility", "The actual quartic is irreducible after algebraic closure of the coefficient field. The polynomial variables b and a remain independent; this is not a specialization at b=1 or b=1/3."),
            Item("simple-pole", "norm_ratio_simple_pole", "Actual norm has a simple pole", "The reduced rational-function denominator of N/A is linear. Its pole is computed in the rational function field."),
            Item("quotient", "quarticQuotientEquiv_root", "Actual quartic quotient identifies the generator", "The concrete AdjoinRoot equivalence sends its actual root to the constructed a in F."),
            Item("involution", "involution_fixed_iff", "Full involution fixed-field criterion", "Every element of F is fixed by the actual quadratic involution exactly when it lies in the image of H.")),
        []));
}
