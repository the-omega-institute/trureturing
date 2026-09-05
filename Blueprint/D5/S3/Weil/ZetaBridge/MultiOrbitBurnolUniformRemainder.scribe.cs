using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class MultiOrbitBurnolUniformRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/MultiOrbitBurnolUniformRemainder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constructed common Burnol packet has a coefficient-uniform geometric remainder and realizes a whole finite family of negative full Weil squares.",
        H("Uniform Multi-Orbit Burnol Remainder"),
        Blocks(
            Describe.Lean(DescribeId.Create("multi-orbit-burnol-derived-uniform-remainder"),
                DeclarationHandle.Create(Prefix + "multiOrbitBurnol_uniform_remainder"),
                H("Uniform remainder derived from actual zeta summability"),
                StatementSource.FromAuthor(Disp(F.Id("abs(R_N(a)) <= (1/4)^(N+1) * C_basis * finiteComplexEnergy(a)"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The target union has the exact value minus four times the multiplicity-weighted coefficient energy. The finite exceptional complement vanishes, and the outside peak contributes the quarter-power factor. The summable mixed majorant controls every cross term uniformly in a."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-multi-orbit-full-weil-negative-family"),
                DeclarationHandle.Create(Prefix + "finite_multiOrbit_full_weil_negative_family"),
                H("A genuine injective negative family for the complete zero sum"),
                StatementSource.FromAuthor(Disp(F.Id("exists basis, synthesis is injective and every nonzero coefficient vector has negative full Weil zeroSum"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common finite power depth is chosen using the geometric decay and the analytic multiplicity floor one. The packet itself is constructed from the supplied valid finite orbit frame, so no remainder estimate or interpolation-full-rank axiom is an extra premise.")),
                    Paragraph(Text("The result assumes a finite separated family of nonreal off-line orbits; it does not assert that such an orbit exists. Constants are frame dependent. No RH, prime-side coercivity, computable depth, or infinite-index conclusion is claimed."))),
                DescribeRole.Theorem)), []));
}
