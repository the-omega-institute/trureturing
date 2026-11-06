using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmComparison.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete strict failure criterion", H("The complete strict failure criterion"), Blocks(
            Node("pair_failure_iff", "The strict score criterion", DescribeRole.Theorem,
                "For every 0<a,c<1, the actual pair/full score inequality 2(P_all-1/3)<P_{0,1}-1/3 holds if and only if D>16q and b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))), with q=a(1-a), D=(2a+c)(3-2a-c). Either equality is nonfailure. The actual CFC scores are bound through symmetric_scores; no evaluation bridge is assumed. This scalar-equivalent test concerns the pair label set; the full optimizer theorem additionally needs that set to be active."),
            Node("active_failure_iff", "The actual active-set failure iff", DescribeRole.Theorem,
                "For every 0<a,c<1, b>0 and b^2<a(1-a), all three actual rho_i are PD trace-one states. With A the nonzero effects of the actual optimalPovm, the original strict failure (|A|-1)(P_A-1/3)>2(P_all-1/3) holds if and only if |c-a|<=b AND D>16q AND b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))). The pair-region conjunct is essential. With three active labels the comparison is equality. This binds the strict criterion to the exact optimizer and its active labels, over the complete strict physical domain."),
            Paragraph(Text("Sources: anonymous mechanism manuscript (3 November 2026, anonymous author field, no supplied license grant); the new note by Haobo Ma then Wenlin Zhang (4 November 2026, new-note-only CC BY 4.0); the literal old byline Wenlin Zhang and Haobo / trureturing. Hyunho Cha credits for symmetric scores and qubit/commuting constructions are retained. The old rational refutation is reused without a new proof. The general all-pure and positive-spectral-floor comparisons remain unresolved by these sources."))
        ), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmcomparison-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), role);
}
