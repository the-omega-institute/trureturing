using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class FibonacciBathObservationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/FibonacciBathObservation.";

    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");
    private static readonly LibraryNoteRef Wheeler =
        LibraryNoteRef.Create("D5/L/Observer/wheeler1999informationphysics");
    private static readonly LibraryNoteRef Shannon =
        LibraryNoteRef.Create("D5/L/Estimation/shannon1948communication");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-level Fibonacci Gibbs bath has a minimum lossless ground-state record of three outcomes.",
        H("A minimal record of the qutrit ground-state observation"),
        Blocks(
            Paragraph(Text(
                "Wheeler's discussion of apparatus-elicited yes-or-no answers in Chapter 19, §19.2 supplies "
                + "the historical context. Here the binary target X is whether the outgoing qutrit is in its "
                + "ground state. B is the outgoing bath basis readout and T is produced from B by a finite "
                + "row-stochastic readout. Shannon's finite entropy and conditional entropy supply the "
                + "information measure. The formal argument uses the repository's Markov equality and "
                + "conditional probability profile theorems.")),
            Describe.Lean(
                DescribeId.Create("terminal-gibbs-implementation"),
                DeclarationHandle.Create(Prefix + "terminalJoint_gibbs_implementation"),
                H("Gibbs preparation and an energy-conserving unitary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ThermalOperations, Wheeler),
                Blocks(Paragraph(Text(
                    "The qutrit has energies 0, 1 and 2 and starts with populations (0, 2/3, 1/3). "
                    + "The independently supplied bath has energies 0 through 5 with multiplicities "
                    + "(1, 1, 2, 3, 5, 8), at inverse temperature log 2. The theorem identifies the "
                    + "appended state with the matrix-exponential Gibbs state of the diagonal bath "
                    + "Hamiltonian. The existing permutation is unitary and conserves total energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("terminal-joint-diagonal"),
                DeclarationHandle.Create(Prefix + "terminalJoint_eq_diagonal"),
                H("Exact terminal joint state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ThermalOperations),
                Blocks(Paragraph(Text(
                    "The entire joint matrix is diagonal. In increasing bath-energy order, its three "
                    + "qutrit rows have per-basis-coordinate numerators (0, 64, 32, 16, 8, 4), "
                    + "(0, 0, 0, 0, 0, 2) and (0, 0, 0, 0, 2, 1), all divided by 282. "
                    + "Lean's kernel checks the rational table against the actual permutation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mutual-information-equality"),
                DeclarationHandle.Create(Prefix + "mutualInformation_eq_iff_preservesGroundPosterior"),
                H("Equality of mutual information and posterior preservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Shannon),
                Blocks(Paragraph(Text(
                    "For any finite joint law of X and B with X binary, the row-stochastic readout "
                    + "gives a Markov chain X → B → T. The equality I(X; T) = I(X; B) holds exactly "
                    + "when P(X = true | B = b) equals P(X = true | T = t) on every positive "
                    + "joint event (b, t). The proof applies the equality case of Markov data "
                    + "processing and reduces equality of Bernoulli laws to their true probabilities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-record-decoder"),
                DeclarationHandle.Create(Prefix + "existsUnique_surjective_recordDecoder"),
                H("Unique decoder on the positive record support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose distinct posterior values label the classes and every class occurs with "
                    + "positive probability. A posterior-preserving randomized record has a unique "
                    + "surjective decoder from its positive-probability symbols onto the classes. "
                    + "For every positive event (b, t), that decoder sends t to the class of b. The proof "
                    + "uses the conditional probability profile theorem on the positive joint support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-posterior-class"),
                DeclarationHandle.Create(Prefix + "groundPosterior_eq_classRate"),
                H("Posterior determined by the bath-energy class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive outcomes at levels 1 through 3 have one class, level 4 has a second "
                    + "class and level 5 has a third class. The bottom level has zero outgoing mass "
                    + "and is assigned to the first class."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-posterior-values"),
                DeclarationHandle.Create(Prefix + "posteriorRate_values"),
                H("The three ground-state posteriors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In class order the ground-state probabilities are 1, 4/5 and 4/7."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-preserving-record-minimum"),
                DeclarationHandle.Create(Prefix + "sixLevel_record_minimal"),
                H("Three outcomes are necessary for exact posterior preservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finite randomized readout preserving the terminal ground-state posterior "
                    + "has at least three positive-probability symbols, since its positive support "
                    + "surjects onto the three realized posterior classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-information-record-minimum"),
                DeclarationHandle.Create(Prefix + "sixLevel_record_minimal_of_mutualInformation_eq"),
                H("Three outcomes are necessary for equality of mutual information"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Shannon),
                Blocks(Paragraph(Text(
                    "For the physical terminal law, equality of the record and full bath mutual "
                    + "information with the ground indicator implies the same three-outcome lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-outcome-attainment"),
                DeclarationHandle.Create(Prefix + "sixLevel_classReadout_attains"),
                H("A three-outcome measurement attains the minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Measure in the bath energy basis and report the deterministic class of the "
                    + "measured coordinate. The classes have outgoing probabilities 88/141, 25/141 and "
                    + "28/141. The readout has three positive outcomes, preserves every positive-event "
                    + "posterior and attains equality of mutual information."))),
                DescribeRole.Theorem))));
}
