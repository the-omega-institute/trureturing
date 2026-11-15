using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorSpectralNormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical spectral exclusion construction", H("OpenBoundaryMPSInteriorSpectralNorm"), Blocks(
            Item("canonicalHbase", "Original spectral exclusion numerator",
                "In the original five-complex canonical coordinate polynomials, form c2 D U (U+D), using h=c4-c1, D=h squared+4 c2 c3, t0=c1-c0 c2, t1=1+c3-c0 c4 and U=h t0 t1-c2 t1 squared+c3 t0 squared.", DescribeRole.Definition),
            Item("canonicalJden", "Real denominator exclusion factor",
                "The factor is the sum of the squares of the coefficientwise real and imaginary parts of the canonical spectral exclusion numerator.", DescribeRole.Definition),
            Item("canonicalW", "Canonical right-seed determinant",
                "W=c2 eta squared+(c1-c4)eta-c3 in the existing complex polynomial ring with thirteen real-coordinate variables.", DescribeRole.Definition),
            Item("canonicalWnorm", "Real right-boundary factor",
                "The sum of the squares of coefficientwise real and imaginary parts of W is an ordinary real polynomial.", DescribeRole.Definition),
            Item("K0", "Literal even-pair coefficient",
                "For four actual real base polynomials g0,g1,g2,g3 and real base polynomials A,B, K0=g0 squared+(A squared+B squared)g3 squared-(1/2)A(g1 squared-g2 squared)-B g1 g2. Every half is a constant polynomial C(1/2).", DescribeRole.Definition),
            Item("H0", "Literal mixed-pair coefficient",
                "H0=2 g0 g3-(1/2)(g1 squared+g2 squared), with scalar half represented by a constant polynomial.", DescribeRole.Definition),
            Item("normg", "Literal REAL13 four-character norm",
                "The ordinary real polynomial is K0 squared-(A squared+B squared)H0 squared. No specialized coefficient algebra is assumed to be a domain.", DescribeRole.Definition),
            Item("spectralCertificate", "Lengthwise certificate assembly",
                "Given the four reduced coefficients and A,B, the expression is X10 times canonicalJden times canonicalWnorm times normg. Its concrete nonvanishing and native consumer are proved by InteriorSpectralWitness and InteriorSpectralAmbiguity.", DescribeRole.Definition),
            Item("character", "Independent complex characters",
                "In any commutative complex algebra, h(E,F)=g0+(1/2)g1(E+F)-(i/2)g2(E-F)+g3 EF. The independent square relations are E squared=a+i b and F squared=a-i b.", DescribeRole.Definition),
            Item("pairK", "Character even coefficient",
                "The generic character expression corresponding to K0 is built in the target commutative complex algebra with the same scalar halves.", DescribeRole.Definition),
            Item("pairH", "Character EF coefficient",
                "The generic character expression corresponding to H0 uses the same four coefficients and scalar half.", DescribeRole.Definition),
            Item("character_opposite", "Correct simultaneous sign pairing",
                "For every commutative complex algebra, all four coefficients and a,b,E,F satisfying the two square relations, h(E,F)h(-E,-F)=pairK+pairH EF. The pair flips both signs together. No nonzero, nonsquare or field-degree premise is used.", DescribeRole.Theorem),
            Item("character_mixed", "Correct mixed opposite pairing",
                "Under the same complete hypotheses, h(-E,F)h(E,-F)=pairK-pairH EF. This follows from the simultaneous opposite pair applied at -E,F.", DescribeRole.Theorem),
            Item("character_four_factor", "Consumed four-character product",
                "Under the same complete hypotheses, h(E,F)h(-E,F)h(E,-F)h(-E,-F)=pairK squared-(a squared+b squared)pairH squared. The proof consumes the two corrected opposite pair identities and E squared F squared=a squared+b squared. A single nonzero specialization of one character does not prove this norm nonzero.", DescribeRole.Theorem),
            Paragraph(Text("This unit proves lengthwise canonical parameter exclusion and pointwise actual ambiguity. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("openboundarympsinteriorspectralnorm-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
