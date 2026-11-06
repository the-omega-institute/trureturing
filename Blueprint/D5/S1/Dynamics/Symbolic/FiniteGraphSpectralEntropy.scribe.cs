using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class FiniteGraphSpectralEntropyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular finite graph walk growth is the degree power, exposing the matrix-to-dynamics bridge.",
        H("Finite Graph Walk Growth and Spectral Entropy"),
        Blocks(
            Paragraph(Text(
                "For a finite simple graph, the total number of length-n walks is the sum of the entries of the nth adjacency-matrix power. "
                + "In the regular case this mass is exactly |V| d^n. "
                + "These identities are the algebraic counting layer for the native symbolic-dynamics entropy bridge; "
                + "they do not assume irreducibility and do not claim the full spectral-radius theorem.")),
            Describe.Lean(
                DescribeId.Create("total-walk-mass"),
                DeclarationHandle.Create(Owner + "walkMass"),
                H("Total walk mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "walkMass G n sums (G.adjMatrix ℕ ^ n) u v over both endpoints. "
                    + "The matrix entries count finite graph walks, so this is the finite-word growth observable consumed by the entropy development."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("regular-walk-growth"),
                DeclarationHandle.Create(Owner + "walkMass_eq_card_mul_pow"),
                H("Regular walk growth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every vertex has degree d, the all-ones vector is an eigenvector of the adjacency matrix with eigenvalue d. "
                    + "Iterating that identity and summing the rows gives walkMass G n = Fintype.card V * d ^ n. "
                    + "No connectedness or aperiodicity hypothesis is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("walk-fibre-interpretation"),
                DeclarationHandle.Create(Owner + "walkMass_eq_sum_walk_cards"),
                H("Walk-fibre interpretation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The total matrix mass is the sum of the finite cardinalities of the endpoint fibres "
                    + "{p : G.Walk u v | p.length = n}. This exposes the finite combinatorial object that will later be compared with realized prefixes of a one-sided graph shift."))),
                DescribeRole.Theorem))));
}
