using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeOrdinaryCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full ordinary character of the actual positive even lattice Sugawara grading.",
        H("Actual Ordinary Lattice Character"),
        Blocks(
            Definition("actual-coefficient", "actualOrdinaryCoefficient", "Literal full-grade dimension",
                "The coefficient at natural energy N is Module.finrank over the complex numbers of the literal eigenspace of sugawaraMode D H 0 with eigenvalue N. No finite surrogate or inserted trace defines it."),
            Definition("actual-character", "actualOrdinaryCharacter", "Vacuum-normalized ordinary character",
                "The character is exp(-2 pi i tau rank/24) times the natural-energy series of the literal full-grade dimensions. Its convergence and theta/eta value are conclusions below."),
            Definition("total-degree", "totalDegree", "Natural total energy",
                "The degree is Int.toNat of the actual label energy, with chargeEnergy plus oscillatorEnergy. Positive definiteness proves that this loses no energy information."),
            Definition("natural-fiber", "NaturalEnergyFiber", "Complete energy-label fiber",
                "Every charge and oscillator occupation of the specified total energy is included; no charge cutoff occurs in this definition."),
            Theorem("natural-fiber-finite", "naturalEnergyFiber_finite", "Finite complete energy fibers",
                "For every LatticeData D with positive definite real Gram matrix and every natural energy N, the complete natural-energy fiber is finite. The proof identifies it with the canonical integral-energy fiber."),
            Theorem("actual-grade-finite", "actualOrdinaryGrade_finiteDimensional", "Finite literal Sugawara eigenspaces",
                "For H with both H*gramComplex D = 1 and gramComplex D*H = 1, positivity identifies the full Sugawara eigenspace with its canonical finite charge cutoff. The existing cutoff basis proves finite dimensionality."),
            Theorem("actual-coefficient-card", "actualOrdinaryCoefficient_eq_card", "Actual dimension counts all energy labels",
                "For the same inverse Gram equations and positivity, actualOrdinaryCoefficient D H N equals Nat.card of EnergyFiber D N. An explicit equivalence places every label into the charge ellipsoid, and the cutoff coefficient basis computes the literal full eigenspace dimension."),
            Theorem("label-factorization", "ordinary_label_series", "Absolutely convergent all-label factorization",
                "For every positive definite D and every complex tau with positive imaginary part, the full label q-series is absolutely summable and equals latticeTheta D tau times the unsigned oscillator occupation sum. Evenness identifies the charge exponent with the exact integral half-norm; Gaussian convergence and the established occupation majorant justify the product of sums."),
            Theorem("dimension-series", "actual_ordinary_series", "Absolutely convergent actual dimension series",
                "For both inverse Gram equations, positive definiteness and positive imaginary part of tau, the unnormalized series of actualOrdinaryCoefficient D H N times exp(2 pi i tau)^N is absolutely summable and has sum latticeTheta D tau times the unsigned occupation sum. Grouping both complex terms and their norms over finite complete energy fibers supplies the dimension coefficients."),
            Theorem("ordinary-character", "actual_ordinary_character", "Actual ordinary character equals theta over eta to the rank",
                "For arbitrary LatticeData D, a complex inverse Gram matrix H satisfying both inverse equations, a positive definite real Gram matrix and tau in the upper half-plane, the vacuum-shifted series of literal Sugawara eigenspace finranks is absolutely summable, has sum latticeTheta D tau divided by eta(tau)^rank, and the defined actualOrdinaryCharacter has that value. The unsigned occupation Euler product and eta nonvanishing evaluate the oscillator factor."),
            Paragraph(Text("All natural energies including zero and every rank including zero are in scope. The unsigned occupation helpers hold for every norm q less than one, including q zero. Rootlessness, unimodularity, rank parity and positive rank are not hypotheses. The reflecting trace character in LatticeThetaCharacter is a separate insertion-dependent quantity.")),
            Paragraph(Text("The ordinary lattice character formula is classical. Mathematical context is the lattice Fock construction of Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster, and the lattice construction in Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1, section 4.1. This proof reuses the canonical actual Sugawara grading, Gaussian convergence, AnalyticIntegerOccupation majorant, AnalyticOddOccupation Euler expansion and Mathlib Dedekind eta product with their original attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("This establishes the ordinary analytic character of the existing lattice algebra and grading. It does not establish a Monster action, orbifold, modular-object or cusp-holomorphy theorem, sewing, string theory or AdS/CFT.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
