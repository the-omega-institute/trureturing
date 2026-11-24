using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class EarnedMemoryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/EarnedMemoryRecovery.";
    private static Formula N => F.Id("n");
    private static Formula At(string name) => new Formula.Subscript(F.Id(name), N);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incidence, frontier, chronological births and completed earned memory " +
        "recover the same actual source data on the law-ready domain.",
        H("Four exact recovery routes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gpo-earned-memory-recovery"),
                DeclarationHandle.Create(Prefix + "earned_memory_recovery"),
                H("Completed backing and exact round trips"),
                StatementSource.FromAuthor(Disp(Seq(
                    At("S"), Comma, Quad, Sp, At("F"), Comma, Quad, Sp,
                    At("T"), Comma, Quad, Sp, At("M")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here F denotes the terminal frontier. The public promise is fixed. The acquired word " +
                        "is the actual first m paid bits. The same deterministic synthesis " +
                        "selects the finite binary coefficients and seed, the finite Moore " +
                        "table, or the whole supplied public coefficient row and its seed. " +
                        "Evaluating the selected code agrees with the shipped generator.")),
                    Paragraph(Text(
                        "Installation reads the actual terminal register and performs the four " +
                        "local writes of earned word, chosen code, cut and birth cursor in " +
                        "the owned mathematical backing. A separately held root binding and " +
                        "continuing Read/update rights are premises, not results of these writes. " +
                        "At later cuts the same code and word must already be retained with " +
                        "synchronized counters and the same live binding; no preservation " +
                        "or repair of synchronization is asserted.")),
                    Paragraph(Text(
                        "Each route returns the same bundle of views, current labelled tree, " +
                        "literal next-cut answers and complete finite future behavior. " +
                        "The chronology is replayed from alpha with the actual rule and " +
                        "includes all serials, update indices, parent addresses and marks " +
                        "through the cut, including the newest bits not paid for at acquisition. " +
                        "Any two conversions commute with the direct map and round trips " +
                        "are identities on the attained images.")),
                    Paragraph(Text(
                        "This applies from the mature deadline onward; for zero target, " +
                        "the singleton zero law is already known and the mature deadline " +
                        "is two. The recovery excludes the private machine presentation, " +
                        "arbitrary observer journals, physical durations and all access grants."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gpo-exact-incidence-route"),
                DeclarationHandle.Create(Prefix + "recover_incidence_exact"),
                H("Incidence recovers the direct bundle"),
                StatementSource.FromAuthor(Disp(Seq(At("S"), Rightarrow, Sp, At("M")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual incidence is decoded to its cut and mature word. " +
                    "Its first m bits determine the same finite code and all views. " +
                    "The frontier decoder reaches the same shape; chronology and " +
                    "memory use their own finite forward replays."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gpo-scalar-time-insufficiency"),
                DeclarationHandle.Create(Prefix + "scalar_time_not_incidence"),
                H("Scalar cut is insufficient in the positive classes"),
                StatementSource.FromAuthor(Disp(Seq(N, Ge, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every such cut constant-zero and constant-one lawful sources " +
                    "give different actual incidences in every binary order cap d≥1 " +
                    "or Moore state cap K≥1. This compares the scalar cut alone with " +
                    "its event-bearing chronology, not arbitrary physical memories."))),
                DescribeRole.Theorem))));
}
