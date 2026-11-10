using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovTriangularColumnSumDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/kurkov2026a396981c1");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every lawful A396981 array satisfies Kurkov's positive-column factorial sum.",
        H("Kurkov's Triangular-Block Column Sum"),
        Blocks(
            Node("f", "The positive-index block sequence",
                "For q>0, f(q) is the unique integer s>=1 satisfying "
                + "s(s-1)/2<q<=s(s+1)/2, namely OEIS A002024. The implementation "
                + "takes the least s with 2q<=s(s+1); the private characterization "
                + "proves equivalence with the source inequalities. Its zero value "
                + "only totalizes the Lean function and supplies no extra source assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsArray", "The literal natural-valued array equations",
                "A has type N -> N -> N. Its zeroth row is one at every column, "
                + "its zeroth column is zero at every positive row, and at positive "
                + "n,q it satisfies A(n,q)=A(n,q-f(q))+(n+f(q)-1)A(n-1,q). "
                + "Natural subtraction agrees with ordinary subtraction on these indices. "
                + "These are the only array hypotheses.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Existence and the complete positive-column identity",
                "There exists A satisfying IsArray, and for every such A, all natural "
                + "n and all k>=1, (A(n,k+f(k)+1):Q) equals the sum over j=0,...,n "
                + "of (A(j,k):Q)*((n+f(k))!:Q)/((f(k)+j)!:Q). "
                + "Factorials are natural factorials cast to Q before ordinary division; "
                + "every denominator is nonzero. The existence witness is constructed by "
                + "well-founded recursion on (n,q). The block inequalities prove "
                + "f(k+f(k)+1)=f(k)+1, so the original array recurrence at the shifted "
                + "column is a first-order row recurrence. Induction on n and the "
                + "factorial successor identity give the inclusive sum, including n=0. "
                + "The prefatory Stirling identity, Conjectures 2–4 and k=0 are outside "
                + "this theorem. Source: Mikhail Kurkov and OEIS Foundation, CC-BY-SA 4.0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a396981-c1-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
