using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sewing;

internal sealed class CanonicalOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ungrouped absolute occupation summability for the literal canonical lattice fields.",
        H("Canonical occupation sewing"),
        Blocks(
            Paragraph(Text("The lattice data D, three integral charges, four external oscillator polynomials, and both signed offsets are arbitrary. For every complex q with norm less than one, including zero, the sum of the norms of the literal occupation terms converges. No rank, Gram positivity, growth, summability or energy-cutoff hypothesis is added.")),
            Node("Occ", "Internal occupations", "All finitely supported natural occupations on Fin D.rank times Nat.", DescribeRole.Definition),
            Node("level", "Oscillator energy", "The existing positive integer oscillator energy, with frequency k+1 at index (i,k).", DescribeRole.Definition),
            Node("b", "Literal monomial state", "The monomial with occupation d and coefficient one in the original oscillator polynomial carrier.", DescribeRole.Definition),
            Node("H", "Factorial coordinate form", "The existing FactorialFockMetric.inner. Its monomial diagonal is the product of occupation factorials; it is used for dual-coordinate resolution. No invariant BPZ or physical unitarity property is asserted.", DescribeRole.Definition),
            Node("A", "Canonical scalar contraction", "The product of the actual canonical outer matrix coefficient with the actual inner coefficient divided by its factorial coordinate weight. The intermediate charge is beta+gamma and the mode shifts are r+level(d) and s-level(d).", DescribeRole.Definition),
            Node("sewnTerm", "Radially damped occupation term", "The exact scalar contraction A multiplied by q to the occupation energy. Every occupation is retained separately.", DescribeRole.Definition),
            Node("creationCoordinate", "Creation occupation numerator", "The finite product of (alpha(i)/(k+1)) to the occupation multiplicity, obtained from the original creation exponential.", DescribeRole.Definition),
            Node("canonical_sewing_summable", "Absolute canonical occupation summability", "For every D, alpha, beta, gamma, u, v, w, p, r, s and q with norm(q)<1, Summable holds for d mapped to norm(sewnTerm D alpha beta gamma u v w p r s q d). The proof first derives the factorial creation coefficient from the actual polynomial derivative identity. Both branches of normalMinusOne give a finite exact coefficient recurrence, including the charge zero mode. Induction on the actual descendant word yields a row bound C(1+level(d))^K L^degree(d) and a complementary column bound S(1+level(d))^J times the product of (B/(k+1))^d(i,k)/d(i,k)!. Their product is summable after polynomial/geometric absorption. A finite expansion in the four external polynomials and exact cancellation of the inner factorial coordinate weight identify the literal canonical summands. All estimates are uniform in the signed modes and are proved before internal occupations are summed.", DescribeRole.Theorem),
            Paragraph(Text("The original field definitions and normal products retain their Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions through the imported sources. Mathlib supplies multivariate polynomial derivatives, finite-support products, exponential and geometric estimates, and summability comparison. The repository integer-occupation character is used only after an actual-coefficient estimate. This is a new formal coefficient-estimate and summability proof in the repository; no external-literature novelty is claimed.")),
            Paragraph(Text("This scalar factorial-coordinate result includes rank-one Gram [2] and keeps arbitrary lattice data because the proof needs no additional restriction. It does not identify the form with BPZ, prove an invariant Hilbert metric, vector or operator convergence, boundary convergence, analytic channel reassociation, full CFT sewing, a Monster construction, or a string/AdS correspondence. Grouping by homogeneous energy and identifying radial canonical products remain separate downstream obligations."))),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("canonical-occupation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
