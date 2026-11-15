using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical REAL13 spectral exclusion and actual ambiguity", H("Canonical spectral exclusion"), Blocks(
            Item("canonical_exclusion_actual_ambiguity", "Nonzero canonical certificate with actual raw interior ambiguity",
                "For each p,q at least one, P(p,q) is nonzero and for every canonical real x with sigma positive, P(p,q)(x) nonzero, and every e squared=D(coreCoordinates x), there exists a nonzero actual binary bond-two MPS of length N=(p+2)+q with exactly the same ENTIRE raw two-site interior as the canonical state with left L, cores A0,A1 and physical right sqrt(sigma)(1,eta), and no unit complex phase relation to that state. The proof consumes certificate_native, BOTH true native target PosDef conclusions, and the actual public nonzero_locus_actual_ambiguity through the conditional native endpoint and raw_amplitude. Native right is u^N S inverse times the original right. The outer G squared congruence remains outside the right transfer iterate. No observed-Q3 or full-actual-image density statement is asserted.", DescribeRole.Theorem),
            Paragraph(Text("This is canonical parameter exclusion and pointwise actual ambiguity. Observed-Q3 descent and genericity in the full actual image remain later obligations. Full C9 remains open and solved-open-problem KPI is zero.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralambiguity-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
