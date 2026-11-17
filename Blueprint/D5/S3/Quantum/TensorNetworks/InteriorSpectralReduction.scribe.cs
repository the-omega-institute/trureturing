using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralReductionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical spectral exclusion construction", H("InteriorSpectralReduction"), Blocks(
            Item("MX", "Multiplication by the first real spectral coordinate",
                "The literal four by four matrix has columns encoding x times the basis (1,x,y,r), using x squared=(r+A)/2, xy=B/2 and rx=A x+B y. Halves are real constant polynomials.", DescribeRole.Definition),
            Item("MY", "Multiplication by the second real spectral coordinate",
                "The literal four by four matrix encodes y times the same basis using y squared=(r-A)/2, xy=B/2 and ry=B x-A y. No matrix-target commutative evaluation is defined.", DescribeRole.Definition),
            Item("coefficients", "Finite actual monomial sum",
                "For an ordinary polynomial G in two spectral variables over the actual REAL13 base, coefficient j is the sum over the finite support of G of coeff(G,m) times entry j of MX to the power m0 times MY to the power m1 applied to (1,0,0,0). The order is fixed and no matrix-commutation theorem is needed.", DescribeRole.Definition),
            Item("monomial_evaluation", "Ordered monomial reduction",
                "For any commutative ring T, ring map alpha from the actual REAL13 base, A,B and x,y,r satisfying the five displayed multiplication-table identities, the row (1,x,y,r) paired with the mapped ordered matrix monomial applied to (1,0,0,0) equals x to the power i times y to the power j for all natural i,j. The proof uses finite eigen-row identities and induction on powers.", DescribeRole.Theorem),
            Item("coefficients_evaluation", "Four literal coefficients evaluate to the original polynomial",
                "For every such target, map, parameters and five multiplication-table identities, and every G in the two spectral variables, eval2(alpha,(x,y),G)=alpha(g0)+alpha(g1)x+alpha(g2)y+alpha(g3)r, where each gj is the literal finite support sum. No domain or field premise is added.", DescribeRole.Theorem),
            Paragraph(Text("This finite reduction is consumed by the nonzero lengthwise canonical exclusion certificate and its pointwise actual ambiguity theorem. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The existing Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralreduction-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
