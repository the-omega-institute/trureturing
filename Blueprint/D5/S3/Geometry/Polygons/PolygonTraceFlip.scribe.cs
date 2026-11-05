using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonTraceFlipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective flips between complete conditioned polygon trace fibres",
        H("Removing one observed ear by an actual diagonal flip"),
        Blocks(Describe.Lean(DescribeId.Create("polygon-trace-flip-injective"),
            DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonTraceFlip.actual_flip_trace_injective"),
            H("The conditioned flip is injective"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Vertices are ZMod(n), chords are Sym2(ZMod(n)), and ear(i) is the unordered chord with endpoints i-1 and i+1. IsTriangulation means that every chord is an internal diagonal, no two chords cross in cyclic order, and every missing internal diagonal crosses a present chord. EarCenters(T) consists of all i whose ear(i) belongs to T.")),
                Paragraph(Text("ConditionFiber(P,Q,H,R) is the subtype of all such finite chord sets T with P contained in EarCenters(T), Q disjoint from EarCenters(T), and EarCenters(T) intersect H equal to R. It includes every actual completion, including empty fibres. In the displayed statement n is arbitrary with n at least 14 and NeZero(n); P,Q,H,R are arbitrary finite vertex sets. Every pair of ears centred in P union Q union H is noncrossing, H is disjoint from P union Q, h belongs to H, and R is contained in H with h erased.")),
                Paragraph(Text("Write gamma=ear(h). For T in the fibre with trace insert(h,R), gamma belongs to T. The exact supplier IsTriangulation.existsUnique_isFlipReplacement selects delta, an internal diagonal absent from T, for which U=insert(delta,erase(T,gamma)) is an actual triangulation. The displayed Flip is actual_flip_trace_map with the hypotheses just stated; it sends the entire chord set T to U and retains the conditioned-fibre proof.")),
                Paragraph(Text("Maximality of T supplies a chord crossing delta. Noncrossing in U forces that chord to be gamma, so delta crosses gamma. Since all designated ears are mutually noncrossing, delta cannot be the ear at any centre in P union Q union H. The original parent PolygonConditionedFan.ear_injective distinguishes the erased ear from every other designated ear. Consequently every forced ear in P survives, no forbidden ear in Q appears, and the observed trace becomes exactly R.")),
                Paragraph(Text("For reconstruction, suppose two inputs produce the same U. Each replacement delta is the unique chord of U crossing gamma: every retained chord was in an input containing gamma and therefore cannot cross it. Thus the two replacement diagonals agree. Erasing this common delta gives equal copies of T with gamma erased; reinserting gamma recovers equal entire input chord sets. This proves injectivity across inputs, beyond the supplier's uniqueness of a replacement for a fixed input.")),
                Paragraph(Text("The consumed cardinality consequence actual_flip_trace_card_le follows by Fintype.card_le_of_injective. It compares the complete trace fibres with insert(h,R) and R, and supplies the one-ear step in PolygonStrictNormalization.actual_weight_antitone. The injective map also supplies the map whose missing image point yields actual_singleton_strict in that owner.")),
                Paragraph(Text("The original parent PolygonConditionalCounts.allEquiv identifies the two triangulation predicates by the identity on entire chord sets in both directions. The 69 declarations of PolygonCatalanSupplier are the sole shared source; this owner contains exactly the 32 additional licensed flip declarations with their original ClusterAlgebras names and proof bodies. Their source revision, spans, authors and Apache-2.0 license are specified in docs/reports/licenses/cluster-algebras-polygon-third-party.md. The conditioned trace construction and reconstruction are repository derivations; the diagonal-flip supplier is licensed reuse.")),
                Paragraph(Text("The result asserts injectivity, not surjectivity. It does not assume positivity of any fibre or restrict to selected completions. Strictness requires an actual conditioned triangulation outside the image, supplied separately by the two-crossing fan construction."))),
            DescribeRole.Theorem)), []));

    private static Formula X(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open, f, Close) : f;
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    private static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    private static Formula Member(Formula a, Formula b) => R(a, InMacro, b);
    private static Formula Union(Formula a, Formula b) => R(a, Cup, b);
    private static Formula Vertex => C("ZMod", X("n"));
    private static Formula Sets => C("Finset", Vertex);
    private static Formula Designated => Union(Union(X("P"), X("Q")), X("H"));
    private static Formula EarCondition => All("i", Vertex, Imp(Member(X("i"), Designated),
        All("j", Vertex, Imp(Member(X("j"), Designated),
            Seq(Neg, C("Cross", C("ear", X("i")), C("ear", X("j"))))))));
    private static Formula Statement()
    {
        Formula body = C("Injective", C("Flip", X("P"), X("Q"), X("H"), X("R"), X("h")));
        body = Imp(R(X("R"), Subseteq, C("erase", X("H"), X("h"))), body);
        body = Imp(Member(X("h"), X("H")), body);
        body = Imp(C("Disjoint", X("H"), Union(X("P"), X("Q"))), body);
        body = Imp(EarCondition, body);
        body = All("h", Vertex, body);
        foreach (var v in new[] { "R", "H", "Q", "P" }) body = All(v, Sets, body);
        return All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp,
            Imp(R(D(1,4), Leq, X("n")), body)));
    }
}
