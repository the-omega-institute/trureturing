using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Pairing;

internal sealed class FiniteDegreePairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite degree support makes a raising-power geometric inclusion an isometry for a sesquilinear basis pairing.",
        H("Finite-degree sesquilinear pairing"),
        Blocks(
            Paragraph(Text("The full-telescope escape audit remains unfinished for every public theorem in this source, including its support and expansion helpers. The missing realization, exact reconstruction, lawful template application, whole-family variation, sensitivity and observational-dependence evidence is disclosed at https://github.com/the-omega-institute/trureturing/issues/25857. The issue is not a validated registration. The original BRST operators have not been shown here to satisfy hH or hA; cohomology, no-ghost and the full programme remain outside this result.")),
            Paragraph(Text("Let b be a genuine basis of a complex module V. Supported b P x means that every nonzero basis coefficient of x satisfies P. A sesquilinear form is expanded over the finite supports of both arguments, with conjugation in its first coefficient. The degree map d is integer-valued, so the selection rule d i + d j = 0 remains valid for signed degrees.")),
            Describe.Lean(DescribeId.Create("finite-double-expansion"), Handle("form_expansion"),
                H("Finite double expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The form of two arbitrary vectors is the finite double sum of basis coefficients and basis pairings. The first coefficient is conjugated by the semilinear map."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("raising-power-support"), Handle("raising_power_support"),
                H("Sector-preserving degree growth"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An operator whose basis transitions preserve the sector and raise d by at least one sends a d=0 sector-supported vector through (-A)^r into the same sector with degree at least r. This is an algebraic support statement and does not construct the operator from BRST data."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("powers-orthogonal"), Handle("powers_orthogonal"),
                H("All positive cross terms vanish"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed degree selection rule and the two lower degree bounds force every pairing H ((-A)^r x) ((-A)^s y) to vanish when r+s is positive. The proof expands the finite supports and cancels every basis cross term individually."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-inclusion-isometry"), Handle("finite_inclusion_isometry"),
                H("Finite geometric inclusion isometry"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least one, the finite geometric sum from r=0 through n-1 has the same pairing as its r=0 inclusion on d=0 sector-supported vectors. The preceding cross-term theorem removes every summand except (0,0); no positivity, nondegeneracy, inverse, nilpotence or analytic completion is assumed."))), DescribeRole.Theorem)
        )));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + name);
}
