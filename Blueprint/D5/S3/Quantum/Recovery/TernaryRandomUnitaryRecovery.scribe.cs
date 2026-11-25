using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class TernaryRandomUnitaryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Exact recovery for a three-branch commuting random-unitary channel.",
            "evidence-not-specified-by-formal-manifest"),
        H("Nonunitary optimal recovery for three commuting branches"),
        Blocks(
            Entry("commuting-branches", "branches_commute", "Commuting unitary branches",
                "The diagonal phase columns are (1, −i, i, 1), (1, i, 1, −i), and (1, 1, −i, i)."),
            Entry("noise-channel", "channel_action", "Equal-weight channel action",
                "The actual CPTP noise acts by averaging the three unitary conjugations."),
            Entry("cptp-bound", "score_le", "Upper bound for all CPTP decoders",
                "At the maximally mixed input with an untouched reference, the score of every CPTP decoder is at most 1/4 + √3/6. "
                + "The canonical Kraus trace identity uses the conjugated diagonals of the decoder Kraus matrices. "
                + "Trace preservation bounds their squared row norms. The Hermitian slack M satisfies M² = 4√3 M, "
                + "so the loss in each coordinate column is a sum of squared moduli divided by 4√3."),
            Entry("kraus-action", "optimalDecoder_action", "Two diagonal Kraus operators",
                "Put a = 2√3/3 − 1 and ω = (−1 − i√3)/2. The two diagonals are the conjugates of "
                + "(1,a,a,a) and √(1−a²)(0,1,ω,ω²). Their coordinatewise squared moduli sum to one."),
            Entry("attainment", "score_attained", "Attainment of the exact CPTP endpoint",
                "The two conjugated Kraus diagonals lie in the kernel of the slack, so the decoder attains 1/4 + √3/6."),
            Entry("strict-unitary-bound", "unitary_score_lt", "Strict bound for every unitary decoder",
                "For an arbitrary unitary decoder, equality would force unit squared modulus at all four diagonal entries "
                + "and place the conjugated diagonal in the slack kernel. The explicit projector expresses any kernel "
                + "vector as a combination of the two displayed directions. Equal moduli in the last three coordinates "
                + "force the coefficient of the cube-root direction to vanish, which contradicts the first-coordinate modulus and a < 1."),
            Entry("binary-bound", "no_binary_representation", "Three branches are necessary",
                "The checked binary recovery theorem gives a unitary optimum in every positive dimension and allows zero weights. Therefore this channel has no one- or two-branch random-unitary representation."),
            Paragraph(Text(
                "The separate dimension bound uses simultaneous diagonalization of commuting normal matrices and the "
                + "Li–Tam bound r² ≤ d for an extreme complex correlation matrix of rank r and size d. "
                + "For d ≤ 3 a maximizing extreme correlation matrix has rank one and yields a diagonal unitary decoder.")))));

    private static DocumentBlock Entry(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
