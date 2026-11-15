using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-length spectral clearing witness", H("Actual all-length spectral clearing witness"), Blocks(
            Item("canonicalPoint", "The original canonical thirteen-coordinate witness",
                "The point is (0,0,1/2,0,1,0,0,0,0,0,1,1,1). Thus its core is the existing spectral witness, sigma=1 and eta=1+i.", DescribeRole.Definition),
            Item("native_b_witness", "The complete raw-right scalar survives",
                "For every p,q at least one, let N=(p+2)+q. The actual b(p,q), evaluated at sector(witnessC,1), nativeLeft(witnessC,1), nativeRight(witnessC,1,N,(1,1+i)) and z(witnessC,1), is nonzero. The public fixed_witness_extraction identifies these data with the same accepted sector (2,0,1), left (1,1), z=1 and right (1/2)^N times (1,i). The exact sixteen-coordinate scale identity and b_right_scale multiply the existing b_nonzero evaluation by the nonzero real quartic ((1/2)^N)^4. No length-dependent scalar is dropped.", DescribeRole.Theorem),
            Item("H_witness", "The actual cleared numerator has a nonzero physical value",
                "For every p,q at least one, H(p,q) evaluated at the real spectral point (1,0) followed by canonicalPoint is nonzero. The exact physical clearing equality is used at the admissible fixed witness. A zero H would force the actual native b evaluation to vanish, contradicting native_b_witness. No complex-valued clearing theorem or fraction-field evaluation is assumed.", DescribeRole.Theorem),
            Item("freeCore", "Unbarred free spectral coordinates",
                "In COMPLEX13 ordered as c0,c1,c2,lambda,mu,barc0,barc1,barc2,barlambda,barmu,eta,bareta,sigma, c3=-c2 lambda mu and c4=c1+c2(lambda+mu).", DescribeRole.Definition),
            Item("freeBarCore", "Independent barred spectral coordinates",
                "The barred copy uses independent polynomial variables, with barc3=-barc2 barlambda barmu and barc4=barc1+barc2(barlambda+barmu). No analytic conjugacy is imposed.", DescribeRole.Definition),
            Item("baseAssignment", "Literal FREE COMPLEX13 map on the existing REAL13 base",
                "Map each real part of cj to (cj+barcj)/2 and each imaginary part to -(i/2)(cj-barcj); sigma maps to the free sigma, and eta real and imaginary parts use the same split of eta,bareta. All halves are scalar coefficient polynomials.", DescribeRole.Definition),
            Item("phi", "Polynomial base map",
                "The map is eval2Hom(C composed with Complex.ofRealHom,baseAssignment). Its injectivity is neither assumed nor required.", DescribeRole.Definition),
            Item("E", "First free root", "E=c2(lambda-mu).", DescribeRole.Definition),
            Item("F", "Second independent free root", "F=barc2(barlambda-barmu).", DescribeRole.Definition),
            Item("swapE", "First literal free-variable swap",
                "The existing renameEquiv exchanges free lambda and mu, fixes every mapped canonical base coordinate, and maps E to -E while fixing F.", DescribeRole.Definition),
            Item("swapF", "Second literal free-variable swap",
                "The existing renameEquiv exchanges free barlambda and barmu, fixes every mapped canonical base coordinate, and maps F to -F while fixing E.", DescribeRole.Definition),
            Item("normg_nonzero", "Free-orbit nonvanishing of the actual lengthwise norm",
                "For every p,q at least one, normg of the actual four reduced g(p,q) and actual discriminant projections is a nonzero REAL13 polynomial. The witness evaluates the first free character to the nonzero physical H value: the cross is exactly one. The two polynomial automorphisms fix the mapped g coefficients and flip independent roots. Injectivity of these automorphisms and the polynomial-domain product prove all four character factors nonzero. The corrected character identity identifies their product with phi(normg); normg=0 would map to zero. No base-map injection, specialized-algebra domain, field degree, nonsquare premise, or norm-at-the-witness argument is used.", DescribeRole.Theorem),
            Item("P_nonzero", "Literal nonzero REAL13 certificate",
                "For each p,q at least one, P(p,q) is nonzero. At canonicalPoint, Jden=1/64 and Wnorm=1; sigma is the nonzero coordinate polynomial. The norm factor is nonzero by the free-orbit proof, independently of its value at that witness. Multiply these nonzero polynomials in the real polynomial domain.", DescribeRole.Theorem),
            Paragraph(Text("The physical witness proves the nonzero free character used in the orbit product. It does not assert that normg or P is nonzero at that specialization. The completed certificate and native positive-environment proofs are consumed by InteriorSpectralAmbiguity. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI is zero.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralwitness-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
