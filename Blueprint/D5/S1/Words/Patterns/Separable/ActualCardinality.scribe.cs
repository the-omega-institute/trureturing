using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ActualCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual minimum-cut partitions identify the literal avoidance and indecomposable counts.",
        H("Actual Separable-Permutation Cardinalities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-signed-minimum-cut-enumeration"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCardinality.actual_signed_cut_enumeration"),
                H("Disjoint minimum-cut enumeration"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("d", F.Id("s"), F.Id("n")), Eq,
                    Call("sum", Seq(D(0), Lt, F.Id("m"), Lt, F.Id("n")),
                        Seq(Call("b", F.Id("s"), F.Id("m")), Times,
                            Call("a", Seq(F.Id("n"), Minus, F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "U(n) is the actual subtype of literal permutations avoiding 2413 and 3142; "
                        + "J(s,n) consists of the members with no proper cut of sign s. D(s,n) "
                        + "consists of the members admitting a proper cut, with no padding at "
                        + "length zero or one. Their cardinalities are a, b and d respectively.")),
                    Paragraph(Text(
                        "For every Boolean sign and every natural length, the theorem supplies "
                        + "an equivalence from D(s,n) to the dependent sum over 0<m<n of "
                        + "J(s,m) times U(n-m). Its index is a minimum cut of the original "
                        + "actual permutation. The finite sum above is the exact cardinality "
                        + "of that disjoint union, including the empty index sets at n=0 and n=1.")),
                    Paragraph(Text(
                        "The proof constructs the least-cut partition and proves its "
                        + "injectivity from minimum-cut uniqueness. Each fiber then uses the "
                        + "frozen actual minimum-cut Cartesian equivalence, with an explicit "
                        + "length transport. It does not import the unfrozen greatest-cut enumeration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-shifted-schroder-cardinalities"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCardinality.actual_schroder_cardinality"),
                H("The exact large and shifted small Schroder counts"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                    Call("a", F.Id("n")), Eq,
                    Call("largeSchroder", Seq(F.Id("n"), Minus, D(1))),
                    Sp, Land, Sp, Call("b", F.Id("s"), F.Id("n")), Eq,
                    Call("smallSchroder", F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The empty actual avoiding class has cardinality one. For all positive "
                        + "n, a(n)=largeSchroder(n-1). For every sign and every natural n, "
                        + "b(s,n)=smallSchroder(n), using the pinned Mathlib shifted definition: "
                        + "smallSchroder(0)=smallSchroder(1)=1 and "
                        + "2*smallSchroder(r+1)=largeSchroder(r) for r>0. "
                        + "In particular both actual indecomposable classes have cardinality "
                        + "one at n=0 and n=1.")),
                    Paragraph(Text(
                        "Only for n>=2, twice either indecomposable cardinality equals a(n), "
                        + "and d(s,n)=b(not s,n). At lengths zero and one, d(s,n)=0. "
                        + "The theorem retains these genuine boundaries instead of padding "
                        + "proper signed classes or asserting sign-half at the singleton.")),
                    Paragraph(Text(
                        "Value complementation exchanges the literal forbidden patterns and "
                        + "the cut sign, proving equal indecomposable counts. The frozen "
                        + "proper-sign/blocked-opposite interface and the actual finite "
                        + "complement partition give sign-half. Minimum-cut enumeration then "
                        + "gives a(n)=2*a(n-1)+sum(1<m<n,a(m)*a(n-m)); strong induction "
                        + "identifies the pinned large Schroder recurrence, and natural-number "
                        + "cancellation gives the shifted small counts.")),
                    Paragraph(Text(
                        "These are source-faithful known enumeration bridges and reusable "
                        + "actual-carrier results, not a claim of mathematical originality, "
                        + "count-ratio asymptotics, an infinite limiting law, or completion "
                        + "of the full derangement-ratio conjecture."))),
                DescribeRole.Theorem))));
}
