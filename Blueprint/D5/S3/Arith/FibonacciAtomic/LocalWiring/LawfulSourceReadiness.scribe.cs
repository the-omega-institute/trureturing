using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class LawfulSourceReadinessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/LawfulSourceReadiness.";
    private static Formula N => F.Id("n");
    private static Formula Dd => F.Id("d");
    private static Formula K => F.Id("K");
    private static Formula At(string id, Formula i) => new Formula.Subscript(F.Id(id), i);
    private static Formula Vn => At("v", N);
    private static Formula Class(string letter, Formula bound) =>
        new Formula.Subscript(Seq(Mathcal, Grp(F.Id(letter))), bound);
    private static Formula Thresholds => Seq(
        N, Ge, Sp, D(2), Comma, Sp, Vn, Eq, At("F", N), Minus, D(1), Quad, Sp,
        Class("R", Dd), Colon, Sp, Vn, Ge, Sp, D(2), Dd, Quad, Sp,
        Class("M", K), Colon, Sp, Vn, Ge, Sp, D(2), K, Minus, D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The current labels and all literal next-cut presence replies require only " +
        "agreement through the bits already born. Complete finite future behavior " +
        "requires agreement of the whole output stream.",
        H("Individual and uniform readiness for two lawful source classes"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-lawful-source-readiness"),
            DeclarationHandle.Create(Prefix + "lawful_source_readiness"),
            H("Attained-fiber criteria and exact uniform thresholds"),
            StatementSource.FromAuthor(Disp(Thresholds)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "At a reached cut n≥2, the input is already acquired current incidence " +
                    "or terminal boundary. Its inverse yields the attained epoch and the " +
                    "mature ordered word of v_n bits. Among legal streams compatible with " +
                    "that word, current labelled-tree recovery and answering every literal " +
                    "next-cut presence address before the update are each equivalent to " +
                    "agreement through the B_n bits already born.")),
                Paragraph(Text(
                    "Complete future behavior means every finite word of actual Read and " +
                    "Update actions, including absent-address replies and the physical " +
                    "incidence and labelled successor after each update. Adaptive policies " +
                    "receive the same accessible reply history and their fixed independent " +
                    "local inputs, not the task snapshots. A differing source digit is " +
                    "distinguished by finitely many real updates and a literal Read reply; " +
                    "no private state names, timing or work coordinates are compared.")),
                Paragraph(Text(
                    "For each task separately the thresholds apply to unknown-order binary " +
                    "recurrences of order at most d≥0, or autonomous unary Boolean Moore " +
                    "sources with a nonempty carrier of size at most K≥1. At the threshold, " +
                    "the original finite synthesizer runs on the required initial part of " +
                    "the mature word, produces an extensionally correct generator and " +
                    "simulates the actual service. Order zero gives the known zero law.")),
                Paragraph(Text(
                    "Below threshold, the actual sharpness witnesses share the full mature " +
                    "word and therefore the same acquired geometry, but disagree at the " +
                    "first bit of a nonempty newest birth batch. This defeats one uniform " +
                    "recovery rule for each task; particular attained fibers may be ready " +
                    "sooner. There is no claim about paid queries, minimum total resources " +
                    "or implementing an observer's source acquisition."))),
            DescribeRole.Theorem))));
}
