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
                DescribeId.Create("actual-shifted-schroder-cardinalities"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCardinality.actual_schroder_cardinality"),
                H("Actual reconstruction, convolution and Schroder counts"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                    Call("a", F.Id("n")), Eq,
                    Call("largeSchroder", Seq(F.Id("n"), Minus, D(1))),
                    Sp, Land, Sp, Call("b", F.Id("s"), F.Id("n")), Eq,
                    Call("smallSchroder", F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "U(n) is the actual subtype of literal permutations avoiding 2413 and 3142; "
                        + "J(s,n) consists of the members with no proper cut of sign s. D(s,n) "
                        + "consists of the members admitting a proper cut, with no padding at "
                        + "length zero or one. Their cardinalities are a, b and d respectively.")),
                    Paragraph(Text(
                        "For every Boolean sign and every natural length, this same theorem "
                        + "exports an equivalence from D(s,n) to the dependent sum over 0<m<n "
                        + "of J(s,m) times U(n-m). Its returned index is a minimum cut of the "
                        + "input, and the actual blockSum of its returned factors equals the "
                        + "input permutation after the explicit dependent-length transport "
                        + "m+(n-m)=n. Thus its contract certifies reconstruction, not just "
                        + "an index-preserving bijection. It also exports the convolution "
                        + "d(s,n)=sum(0<m<n,b(s,m)*a(n-m)), including empty index sets.")),
                    Paragraph(Text(
                        "Inside this substantive count proof, frozen CappedExploration.recover "
                        + "supplies the compatible sign, minimum cut and uniqueness on the "
                        + "opposite-blocked actual carrier. Each fiber reuses the frozen actual "
                        + "minimum-cut Cartesian equivalence and its reconstruction certificate. "
                        + "No separate enumeration theorem or unfrozen greatest-cut supplier is used.")),
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
