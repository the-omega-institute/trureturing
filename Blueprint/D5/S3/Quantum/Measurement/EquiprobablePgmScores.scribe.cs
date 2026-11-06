using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmScoresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmScores.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact PGM evaluation on actual states", H("Exact PGM evaluation on actual states"), Blocks(
            Node("diagonal_score", "The full diagonal support formula", DescribeRole.Theorem,
                "For every d,N with N>0, every nonnegative real family p_i(x), and every label set B, the actual old CFC pgmScore of rho_i=diag(p_i) is (1/N) sum_(i in B) sum_x p_i(x)^2/(sum_(j in B) p_j(x)). A zero spectral mass has inverse zero. Empty B and singular support are permitted. Normalization sum_x p_i(x)=1 is not needed for the evaluation; with it these are actual density matrices. This universal diagonal formula is the supplier for the commuting control and dimension-one minimality."),
            Node("symmetric_scores", "Both actual symmetric scores", DescribeRole.Theorem,
                "For every real a,b,c with 0<a,c<1, the actual original-prior restricted and full CFC scores of rho(a,b,c) satisfy P_{0,1}-1/3=2b^2/(3sqrt(a(1-a))) and P_all-1/3=4b^2/(3sqrt(D))+2(c-a)^2/(3D), D=(2a+c)(3-2a-c). The evaluation does not need a pair determinant hypothesis. When b^2<=a(1-a), the pair is physical, including the singular equality case; strict determinant positivity gives the full strict-PD setting. The proof evaluates the existing diagonal CFC, including its support inverse, and multiplies the actual matrices inside the existing score definition. Hyunho Cha is credited for these symmetric calculations."),
            Paragraph(Text("Sources: anonymous mechanism manuscript (3 November 2026, anonymous author field, no supplied license grant); the new note by Haobo Ma then Wenlin Zhang (4 November 2026, new-note-only CC BY 4.0); the literal old byline Wenlin Zhang and Haobo / trureturing. Hyunho Cha credits for symmetric scores and qubit/commuting constructions are retained. The old rational refutation is reused without a new proof. The general all-pure and positive-spectral-floor comparisons remain unresolved by these sources."))
        ), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmscores-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), role);
}
