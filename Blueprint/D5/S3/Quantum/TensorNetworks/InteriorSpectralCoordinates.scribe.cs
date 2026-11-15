using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical spectral exclusion construction", H("InteriorSpectralCoordinates"), Blocks(
            Item("point", "Spectral and canonical indexing",
                "The ordinary Fin15 real assignment has spectral Re(e), Im(e) at indices zero and one, followed by the existing Fin13 canonical coordinates in their unchanged order.", DescribeRole.Definition),
            Item("Frac", "Independent polynomial fractions",
                "A fraction stores two ordinary complex polynomials. Addition, multiplication, inversion and natural powers construct literal numerator and denominator polynomials. Inversion is used only when the interpreted value is nonzero. The real projections use nr dr+ni di and ni dr-nr di over dr squared+di squared, with no polynomial division.", DescribeRole.Definition),
            Item("nativeTerms", "The actual eight complex native entries",
                "For each natural length N the eight expressions are lambda, mu, a, l0, l1, r0, r1, z, with the actual spectral frame, its actual matrix inverse, the diagonal rho gauge, and r=u to the power N times S inverse applied to (1,eta). No native right entry is required nonzero. N=0 remains included.", DescribeRole.Definition),
            Item("numerator", "Literal REAL15 numerators",
                "The sixteen entries alternate the real and imaginary numerators of the eight actual complex entries.", DescribeRole.Definition),
            Item("denominator", "Literal REAL15 denominators",
                "Each coordinate keeps its independently constructed denominator norm square; no common power or degree bound is imposed.", DescribeRole.Definition),
            Item("native_coordinates", "Exact physical ratios and every inverse guard",
                "For every real canonical assignment x, complex e satisfying Admissible(coreCoordinates(x),e), and every natural N, every one of the sixteen real denominator evaluations is nonzero. The vector of numerator evaluations divided by denominator evaluations equals exactly InteriorPolynomial.coordinates of the existing extracted sector, nativeLeft, nativeRight at full length N and raw original right column (1,eta(x)), and z. The proof uses spectral_frame for the frame determinant and all nonzero conjugated entries, native_extraction for detS and the native left row, explicit two by two adjugates, and real complex-division formulas. The same assertion applies separately to e and -e, since only Admissible is used.", DescribeRole.Theorem),
            Paragraph(Text("These concrete coordinates are consumed by the nonzero lengthwise canonical exclusion certificate and its pointwise actual ambiguity theorem. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The existing Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralcoordinates-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
