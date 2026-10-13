using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetTwoStepArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetTwoStepArithmetic.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Q(Formula body) => All(body, B("q", I("Nat")),
        B("hq", Call("NatPositive", I("q"))), B("h4", Call("Dvd", Num(4), I("q"))));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, type);
    private static Formula Matrix => Call("resetMatrix", I("q"));
    private static Formula Carrier => Call("twoStepCarrier", I("q"));
    private static Formula Data => Call("numberedData", I("q"), I("hq"), I("h4"));
    private static Formula Squares => Call("squares", Data);
    private static Formula Histories => Call("History", Call("expandedGraph", Matrix));
    private static Formula Vertex => Call("product", Call("Fin", I("q")), I("Sign"));
    private static Formula Aut => Call("aut", I("q"), I("hq"), I("h4"));
    private static DocumentBlock Record(string name, string id, string title,
        Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual empty/two-edge boundaries, a mod-four path exchange and finite forgetting realize identity plus two unit times.",
        H("Two-step reset paths and the original history action"),
        Blocks(
            Paragraph(Text("Sign is Multiplicative Bool with its original XOR group law; tau is ofAdd true. "
                + "An original reset edge F(i,g) runs from (i,g) to (0,g*tau). An advance A(i,g) runs "
                + "to (i+1,g) only when i.val+1<q. The original label and number zero are retained through "
                + "Alternating.actualEdgeEquiv. R q is the disjoint family D, AA, AF, FA, FF: D is the "
                + "empty path at a vertex and the other constructors store two actual composable edges. "
                + "AA requires i.val+2<q, AF requires i.val+1<q, and FA requires 1<q. No path is "
                + "identified merely because its endpoints or total label agree.")),
            Paragraph(Text("NatPositive(q) means 0<q; Dvd(4,q) means 4 divides q. These hypotheses imply "
                + "q>=4. The active ages have residue zero or one modulo four, so both advances in AAF "
                + "are legal, including near the terminal age. Word q is the tagged sum of one edge and "
                + "three edges. legal imposes the two compositional seams on a triple. The exchange fixes "
                + "every word except the active F(i,g) and A(i,g) A(i+1,g) F(i+2,g) pair. It preserves "
                + "the exact expanded source and target, and preserves legality in both directions.")),
            Record("exchange_involutive", "two-step-path-exchange-involution",
                "The actual one/three-edge exchange is its own inverse",
                All(Call("FunctionInvolutive", Call("exchange", I("h4"))),
                    B("q", I("Nat")), B("h4", Call("Dvd", Num(4), I("q")))),
                "The triple guard compares both actual trailing edges, including the absolute signs. "
                    + "Thus the reverse exchange recovers the same F edge, and a fixed triple cannot "
                    + "become an exchanged triple. Concatenating a left edge with its empty/two-edge "
                    + "suffix, applying this involution and splitting before the last edge gives the "
                    + "square relation. Both uniqueness directions follow from the involution and "
                    + "the unique actual first-edge or last-edge splitting.", DescribeRole.Theorem),
            Record("numberedBoundaryEquiv", "two-step-actual-boundary-numbering",
                "Every actual path has its full coefficient number",
                All(Typed(Call("numberedBoundaryEquiv", I("hq")),
                    Call("Equiv", Call("R", I("q")),
                        Call("product", Call("Edge", Carrier), I("Sign")))),
                    B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))),
                "The two-edge path is joined using the existing product coefficient fibers and the "
                    + "original ordered labels. The additive numbering assigns the identity summand "
                    + "its first number interval and the square summand its second. At the origin, "
                    + "the identity coefficient is one and the FF product coefficient is one. D(0,g) "
                    + "therefore occupies number zero and FF(0,g) occupies number one of the same "
                    + "identity-labelled entry of C=I+B^2. The explicit FF number is checked "
                    + "against the product joining, so this is an equivalence of actual paths and "
                    + "numbered edges, preserving both expanded endpoints.", DescribeRole.Definition),
            Record("endpointSquare", "two-step-endpoint-square-bijection",
                "The square bijection preserves each exact endpoint fiber",
                Q(All(Typed(Call("endpointSquare", I("hq"), I("h4"), I("v"), I("z")),
                    Call("Equiv", Call("BRFiber", I("hq"), I("v"), I("z")),
                        Call("RBFiber", I("hq"), I("v"), I("z")))),
                    B("v", Vertex), B("z", Vertex))),
                "BRFiber contains a left original edge followed by an R boundary; RBFiber contains "
                    + "an R boundary followed by a right original edge. Both retain their compositional "
                    + "seam and the prescribed source v and target z. The twelve guarded square "
                    + "cases are precisely the ordinary splitting and the active F/AAF exchange. "
                    + "The two maps of this equivalence are the back and forth operations used by "
                    + "the original numbered square interface.", DescribeRole.Definition),
            Paragraph(Text("Left rank compares unequal R boundaries with a common SOURCE (i,g). Put "
                + "a=i.val+3 and c=i.val mod4; X denotes FA or FF. The D/AA rank is a. D/AF has "
                + "rank a for c=0,3 and one otherwise; D/X has rank a for c=0,1 and two otherwise. "
                + "AA/AF has rank a for c=1,2 and one otherwise; AA/X has rank a for c=2,3 and "
                + "two otherwise. AF/X has rank a for c=1,3 and two otherwise. FA/FF has rank one. "
                + "Every actual unequal comparison lies in [1,q]. At ages q-2 and q-1 the missing "
                + "AA or AF constructors remove exactly the apparent out-of-range cases. Along a "
                + "common left edge, an unequal initial pair has strictly smaller rank than the "
                + "terminal pair.")),
            Paragraph(Text("Right rank compares unequal boundaries with a common TARGET (j,g). "
                + "Identity versus a two-edge path has rank q-j.val. Two two-edge paths have rank "
                + "one when their last actual edges coincide, and two otherwise. On this fiber, "
                + "equality of the last actual edges is equivalent to equality of their last edge "
                + "kind and source age; their signs follow from the common target. All ranks lie "
                + "in [1,q]. Along a common right edge an unequal terminal pair has strictly smaller "
                + "rank than the initial pair.")),
            Record("finiteForgetting", "two-step-universal-q-square-forgetting",
                "Unrestricted square strips forget after q steps",
                Q(Call("FiniteForgetting", Squares, I("q"))),
                "The left obligation quantifies over every x:Nat->E, every independent y,yPrime:Nat->E "
                    + "and every independent r,rPrime:Nat->R numbered boundary. If both strips satisfy "
                    + "the square relation for i<q with common x, then r(0)=rPrime(0). The right "
                    + "obligation has independent x,xPrime, common y and concludes r(q)=rPrime(q). "
                    + "Equal propagation and the two uniqueness laws force a surviving disagreement "
                    + "to undergo q strict rank steps. Positivity and the upper bound q contradict "
                    + "this, including the final boundary. Common sources on the left and common "
                    + "targets on the right follow solely from the common prescribed row and square "
                    + "endpoints. The opposite rows and opposite endpoints are unrestricted.", DescribeRole.Theorem),
            Record("aut", "two-step-original-unit-time-automorphism",
                "A homeomorphism of the original unlimited histories",
                Q(Typed(Aut, Call("ResetFullAut", I("q")))),
                "SameCutWholeRayBridge constructs the mutually inverse full lifts from numberedData "
                    + "and finiteForgetting. Its historyHomeomorph supplies continuity in the original "
                    + "product/subtype topology and H_shift supplies commutation with the original "
                    + "unit shift. Its numbered_same_cut_whole_ray_image decomposes every full past "
                    + "ray at its original integer cut into components indexed by ALL outgoing "
                    + "numbered C boundaries. numbered_arbitrary_future_preimage covers every legal "
                    + "future of each component, and right forgetting makes different full boundary "
                    + "indices disjoint. D(0,g) and FF(0,g) therefore remain distinct whole rays.", DescribeRole.Definition),
            Record("image_endpointRow", "two-step-actual-image-endpoint-row",
                "The whole image has the row of the numbered square carrier",
                Q(All(Equal(Call("endpointRow", Call("ResetGraph", I("q")),
                    Call("image", Aut, Call("ray", Call("ResetGraph", I("q")), I("alpha"), I("n"))), I("n")),
                    Call("rightMultiply", Call("single", Call("endpoint", Call("ResetGraph", I("q")),
                        I("alpha"), I("n")), Num(1)), Call("expansionMatrix", Carrier))),
                    B("alpha", Histories), B("n", I("Int")))),
                "The finite Parts instance is supplied by image_atCut for this actual image set. "
                    + "The disjoint full-ray decomposition lets each numbered outgoing boundary "
                    + "contribute one endpoint basis vector. Its target is exactly the expanded C "
                    + "target. expanded_adjacency_eq identifies that sum with the original right "
                    + "row of expansionMatrix C, including both equal-endpoint origin contributions.", DescribeRole.Theorem),
            Record("rho_eq", "two-step-genuine-native-rho",
                "The actual native representation equals identity plus Theta squared",
                Q(Equal(Call("linearMap", Call("rho", I("q"), I("hq"), Aut)),
                    Call("endSum", Call("linearIdentity"), Call("power", Call("resetTheta", I("q")), Num(2))))),
                "rho is the existing representation of actual whole-set pushforward, conjugated "
                    + "onto the original integral DimensionGroup. The same-cut endpoint row is "
                    + "transported by the original two-sign coefficient basis, at the same native "
                    + "stage, to z+T(Tz). rho_beam_image identifies this computed set image with "
                    + "the actual automorphism action. The original vertex basis and all colimit "
                    + "stages give equality on the entire integer group. resetTheta is the original "
                    + "unit-time transition; no change of time or integral lattice is used.", DescribeRole.Theorem))));
}
