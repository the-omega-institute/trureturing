using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43D"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43d to the stochastic ellipsoid construction.")),
            Node("claim-2", "integrableOn_t_of_bounded", "integrable On t of bounded",
                "hgt, discharged. The fixed-radius slice t ↦ g t r is integrable on (0,T] because it is bounded and (0,T] has finite measure. Φ ≤ 1/2 supplies the bound.", DescribeRole.Theorem),
            Node("claim-3", "integrableOn_Ioi_of_support", "integrable On Ioi of support",
                "Extending integrability from a bounded window to (0,∞). A profile supported in (0, L] is integrable on Ioi 0 as soon as it is integrable on the window. This is what turns the fixed-window bound into RadialWeightData.radial_bound's Ioi 0 statement.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
