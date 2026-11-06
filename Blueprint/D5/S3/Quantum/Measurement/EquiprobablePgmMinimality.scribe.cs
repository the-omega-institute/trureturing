using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmMinimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmMinimality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PGM minimality and limited pure control", H("Actual PGM minimality and limited pure control"), Blocks(
            Node("singleton_score", "The singleton support endpoint", DescribeRole.Theorem,
                "For every positive N, every PSD trace-one family rho_i on C^d, and every label i, the actual original-prior singleton CFC score is P_{i}=1/N. Singular states are allowed. This follows from the support quarter-power sandwich in the centered identity and includes N=1."),
            Node("dimension_one_score", "Every one-dimensional score", DescribeRole.Theorem,
                "For every N>0, every trace-one one-dimensional matrix family and every nonempty B, P_B=1/N. In dimension one trace normalization fixes every matrix to I; the universal diagonal CFC formula gives the result. Thus the comparison is equality in dimension one."),
            Node("at_most_two_labels", "No violation with at most two labels", DescribeRole.Theorem,
                "For every 0<N<=2, every PSD trace-one ensemble in any finite dimension and every nonempty B, (|B|-1)(P_B-1/N)<=(N-1)(P_all-1/N). This is stronger than restricting B to an optimum’s active set. A singleton has zero centered score by singleton_score; otherwise B is all labels and the comparison is equality. Together with the reused actual three-state qubit rational refutation, this proves minimality d=2,N=3 for violation."),
            Node("pure_pair_population", "The limited pure-pair geometric control", DescribeRole.Theorem,
                "For real 0<z<1 and a pure Bloch vector (x,y,w) with x^2+y^2+w^2=1, membership in the ball x^2+y^2+(w-z)^2<=1-z^2 implies w>=z and (1-w)/2<=(1-z)/2, with the latter reference population positive. The symmetric pure pair has Bloch vectors (+/-sqrt(1-z^2),0,z). This is a limited mechanism restriction, not a general all-pure comparison theorem. The general all-pure and quantitative spectral-floor questions remain open in the supplied sources."),
            Paragraph(Text("Sources: anonymous mechanism manuscript (3 November 2026, anonymous author field, no supplied license grant); the new note by Haobo Ma then Wenlin Zhang (4 November 2026, new-note-only CC BY 4.0); the literal old byline Wenlin Zhang and Haobo / trureturing. Hyunho Cha credits for symmetric scores and qubit/commuting constructions are retained. The old rational refutation is reused without a new proof. The general all-pure and positive-spectral-floor comparisons remain unresolved by these sources."))
        ), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmminimality-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/anonymous2026pgmmechanism")),
        Blocks(Paragraph(Text(prose))), role);
}
