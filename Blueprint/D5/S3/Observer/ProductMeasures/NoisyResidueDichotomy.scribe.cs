using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProductMeasures;

internal sealed class NoisyResidueDichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noisy residue transcripts split into singular and equivalent regimes by energy.",
        H("Noisy Residue Kakutani Dichotomy"),
        Blocks(
            Definition(
                "noisy-residue-law",
                "noisyResidueLaw",
                "Noisy residue coordinate law",
                NoisyResidueLawFormula(),
                "A state residue is passed through its coordinate channel."),
            Definition(
                "pair-local-hellinger-energy",
                "pairLocalHellingerEnergy",
                "Pairwise local Hellinger energy",
                PairEnergyFormula(),
                "The energy compares the two state-dependent coordinate laws."),
            Definition(
                "blind-coordinates",
                "blindCoordinates",
                "Blind coordinate set",
                BlindCoordinatesFormula(),
                "A coordinate is blind when its local Hellinger energy is zero."),
            Definition(
                "infinite-transcript",
                "infiniteTranscript",
                "Infinite observation transcript",
                InfiniteTranscriptFormula(),
                "The transcript evaluates the coordinate observation at one sample."),
            Definition(
                "transcript-law",
                "transcriptLaw",
                "State transcript product law",
                TranscriptLawFormula(),
                "The law is the countable product of a state's coordinate PMFs."),
            Theorem(
                "noisy-residue-product-completion-criterion",
                "noisy_residue_product_completion_criterion",
                "Noisy residue product completion criterion",
                ProductCriterionFormula(),
                "Under local equivalence, singularity is exactly nonsummable energy."),
            Theorem(
                "noisy-residue-independent-completion-criterion",
                "noisy_residue_independent_completion_criterion",
                "Independent transcript completion criterion",
                IndependentCriterionFormula(),
                "Independent observations have the coordinate product law, so the criterion "
                    + "applies to their mapped transcript laws."),
            Theorem(
                "equal-local-laws-zero-energy",
                "equal_local_laws_zero_energy",
                "Equal local laws have zero total energy",
                EqualLawsFormula(),
                "Equality coordinate by coordinate gives zero energy and equal products."),
            Theorem(
                "singleton-output-energy-zero",
                "singleton_output_energy_zero",
                "Singleton outputs have zero energy",
                SingletonOutputFormula(),
                "The unique PMF on a singleton agrees with itself at every coordinate."),
            Theorem(
                "empty-output-has-no-pmf",
                "empty_output_has_no_pmf",
                "Empty outputs carry no PMF",
                EmptyOutputFormula(),
                "Normalization rules out a probability mass function on the empty type."),
            Theorem(
                "local-mutual-ac-is-necessary",
                "local_mutual_absolute_continuity_is_necessary",
                "Local equivalence is necessary",
                LocalAcNecessaryFormula(),
                "A single disjoint coordinate gives finite energy but singular products."),
            Theorem(
                "coordinate-independence-is-necessary",
                "coordinate_independence_is_necessary",
                "Coordinate independence is necessary",
                IndependenceNecessaryFormula(),
                "Two dependent Boolean transcripts share every marginal and zero energy, yet "
                    + "their full laws are singular."))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe(id, declaration, title, statement, explanation, DescribeRole.Definition);

    private static DocumentBlock Theorem(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe(id, declaration, title, statement, explanation, DescribeRole.Theorem);

    private static DocumentBlock Describe(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation,
        DescribeRole role) =>
        StrataLint.Scribe.Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            role);

    private static Formula NoisyResidueLawFormula() =>
        Disp(Equal(
            Call("noisyResidueLaw", F.Id("r"), F.Id("K"), F.Id("x"), F.Id("i")),
            Call("K", F.Id("i"), Call("r", F.Id("i"), F.Id("x")))));

    private static Formula PairEnergyFormula() =>
        Disp(Equal(
            Call("pairLocalHellingerEnergy", F.Id("L"), F.Id("x"), F.Id("y"),
                F.Id("i")),
            Call("energy", Call("L", F.Id("x"), F.Id("i")),
                Call("L", F.Id("y"), F.Id("i")))));

    private static Formula BlindCoordinatesFormula() =>
        Disp(Equal(
            Call("blindCoordinates", F.Id("L"), F.Id("x"), F.Id("y")),
            Call("zeroSet", Call("pairLocalHellingerEnergy", F.Id("L"), F.Id("x"),
                F.Id("y")))));

    private static Formula InfiniteTranscriptFormula() =>
        Disp(Equal(
            Call("infiniteTranscript", F.Id("X"), F.Id("omega"), F.Id("i")),
            Call("X", F.Id("i"), F.Id("omega"))));

    private static Formula TranscriptLawFormula() =>
        Disp(Equal(
            Call("transcriptLaw", F.Id("L"), F.Id("x")),
            Call("productLaw", Call("L", F.Id("x")))));

    private static Formula ProductCriterionFormula() =>
        Disp(new Formula.Logic(
            Call("MutuallySingular", Call("transcriptLaw", F.Id("L"), F.Id("x")),
                Call("transcriptLaw", F.Id("L"), F.Id("y"))),
            FormulaLogicOperator.Iff,
            Seq(Neg, Sp, Call("Summable", Call("pairEnergy", F.Id("L"), F.Id("x"),
                F.Id("y"))))));

    private static Formula IndependentCriterionFormula() =>
        Disp(new Formula.Logic(
            Call("MutuallySingular", Call("mappedTranscriptLaw", F.Id("P"), F.Id("X")),
                Call("mappedTranscriptLaw", F.Id("Q"), F.Id("Y"))),
            FormulaLogicOperator.Iff,
            Seq(Neg, Sp, Call("Summable", Call("pairEnergy", F.Id("L"), F.Id("x"),
                F.Id("y"))))));

    private static Formula EqualLawsFormula() =>
        Disp(And(
            Equal(Call("pairEnergy", F.Id("L"), F.Id("x"), F.Id("y")), D(0)),
            And(
                Equal(Call("totalEnergy", F.Id("L"), F.Id("x"), F.Id("y")), D(0)),
                Equal(Call("transcriptLaw", F.Id("L"), F.Id("x")),
                    Call("transcriptLaw", F.Id("L"), F.Id("y"))))));

    private static Formula SingletonOutputFormula() =>
        Disp(Equal(Call("singletonOutputEnergy", F.Id("i")), D(0)));

    private static Formula EmptyOutputFormula() =>
        Disp(Call("IsEmpty", Call("PMF", Emptyset)));

    private static Formula LocalAcNecessaryFormula() =>
        Disp(Call("ExistsFiniteEnergySingularProductsWithoutLocalEquivalence"));

    private static Formula IndependenceNecessaryFormula() =>
        Disp(Call("ExistsDependentEqualMarginalZeroEnergySingularTranscripts"));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
