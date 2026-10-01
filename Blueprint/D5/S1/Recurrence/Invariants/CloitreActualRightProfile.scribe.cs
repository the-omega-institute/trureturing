using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualRightProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/CloitreActualRightProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Cloitre sequence has every fixed right Fibonacci profile under its full golden and orbit hypotheses.",
        H("Actual Cloitre Right Fibonacci Profiles"),
        Blocks(
            Paragraph(Text(
                "F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "G(n) is the natural floor of (n+1) divided by the golden ratio. "
                + "All indices and offsets are natural numbers; C has positive indices "
                + "and an exterior zero convention.")),
            Node("C", "The actual Cloitre sequence",
                "C(1)=C(2)=1. For N at least three, form the map x to N-C(x) "
                + "on the already defined positive prefix, start at N-1, apply it "
                + "exactly C(N-1) times, and call the selected point g(N). Then "
                + "C(N)=C(g(N))+C(N-g(N)). The immutable finite-prefix construction "
                + "keeps every iterate and both children between one and N-1."),
            Node("D", "The legal prefix domain",
                "D(N) is the closed natural interval from one to N-1."),
            Node("T", "The actual inner map",
                "T(N,x)=N-C(x), with N fixed throughout each orbit."),
            Node("X", "The actual orbit",
                "X(N,i) is the i-th iterate of T(N) at the prescribed origin N-1."),
            Node("d", "The actual depth",
                "d(N)=C(N-1); it varies with the actual sequence output."),
            Node("g", "The actual selected point",
                "g(N)=X(N,d(N))."),
            Node("I", "The right Fibonacci collar",
                "I(q,t) is the closed natural interval from F(q-1) to F(q-1)+t."),
            Node("DepthEntry", "Entry before the prescribed depth",
                "There is an earliest time mu at which X(N,mu) is a periodic "
                + "point of the actual map T(N), and mu is at most d(N). "
                + "All earlier times are outside Function.periodicPts(T(N))."),
            Node("SourceFoundations", "Conditional finite foundations",
                "For 16384 through 131071, 22877*C(n) is at most 15225*n. "
                + "For positive n through 65535, G(n) is at most C(n), and equality "
                + "requires a Fibonacci number or its successor at an index at "
                + "least two, the predecessor of an odd-index Fibonacci number "
                + "at an index at least three, or one of 11, 24, 25, 59. "
                + "DepthEntry holds for N from three through 52. "
                + "These are conditional premises, not independent finite certificates."),
            Node("Hyp21_1", "The complete conditional premise bundle",
                "SourceFoundations holds. For every positive n, "
                + "1<=C(n) and G(n)<=C(n)<=U(n)<=n. U(1)=1. For j at least three "
                + "and F(j)<=n<F(j+1), U(n)=min(n-F(j-2),F(j)). U is nondecreasing "
                + "on positive indices and U(n)<=U(n+1)<=U(n)+1. For every j at "
                + "least two, U(F(j))=C(F(j))=G(F(j))=F(j-1). For every j at "
                + "least three, G(F(j)+1)=C(F(j)+1)=F(j-1)+1. For every q at "
                + "least six and every t, I(q,t) lies in D(F(q)+t), is invariant, "
                + "captures the orbit of every point of that domain, and contains "
                + "all its periodic points. DepthEntry holds for every N at least three. "
                + "No monotonicity of C or arbitrary-width seed is assumed."),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-foundations"),
                DeclarationHandle.Create(Prefix + "actual_foundations"),
                H("Unconditional actual finite-prefix foundations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least three, every actual iterate X(N,i) lies in D(N), "
                    + "and C(N)=C(g(N))+C(N-g(N)). Both conclusions follow from "
                    + "the immutable finite-prefix construction without Hyp21_1. "
                    + "The conditional profile theorem consumes this shared proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full21-3"),
                DeclarationHandle.Create(Prefix + "full21_3"),
                H("Every fixed right width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every function U from natural numbers to natural numbers "
                    + "satisfying Hyp21_1, and for all natural t and k with "
                    + "6*t+6<=k, C(F(k)+t)=F(k-1)+t. "
                    + "The proof uses strong induction on the offset. A positive "
                    + "profile deficit forces the actual selected lower endpoint, "
                    + "a positive deficit two orders below, and an odd actual depth. "
                    + "Three such orders contradict Fibonacci parity. "
                    + "The parity step directly uses GoldenFibDivisibility.fib_dvd_iff "
                    + "at index three. All finite source foundations remain conditional."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string name, string title, string description) =>
        Describe.Lean(DescribeId.Create("cloitre-actual-" + (name == "D" ? "domain" : name.ToLowerInvariant().Replace('_', '-'))),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
