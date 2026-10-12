using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetAlternatingSquaresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula For(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula All(Formula body) => For(body,
        B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))));
    private static Formula EvenAll(Formula body) => For(body,
        B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))),
        B("he", Call("Even", I("q"))));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, type);
    private static Formula Matrix => Call("resetMatrix", I("q"));
    private static Formula Vertex => Call("product", Call("Fin", I("q")), I("Sign"));
    private static Formula Edge => Call("product", Call("Edge", Matrix), I("Sign"));
    private static Formula BEdges => Call("B", I("q"));
    private static Formula REdges => Call("R", I("q"));
    private static Formula BList => Call("List", BEdges);
    private static Formula First(Formula p) => Call("fst", p);
    private static Formula Second(Formula p) => Call("snd", p);
    private static Formula SourceB(Formula x) => Call("sourceB", x);
    private static Formula TargetB(Formula x) => Call("targetB", I("hq"), x);
    private static Formula SourceR(Formula r) => Call("sourceR", r);
    private static Formula TargetR(Formula r) => Call("targetR", I("hq"), r);
    private static Formula Square(Formula r, Formula x, Formula y, Formula s) =>
        Call("Square", I("hq"), r, x, y, s);
    private static Formula Strip(Formula xs, Formula r, Formula s, Formula ys) =>
        Call("Strip", I("hq"), xs, r, s, ys);
    private static Formula Boundary(Formula r) => Call("originalBoundary", I("hq"), r);
    private static Formula LeftChoice => Call("leftSquare", I("hq"), I("x"), I("s"));
    private static Formula RightChoice => Call("rightSquare", I("hq"), I("r"), I("y"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed original reset edges, endpoint square bijections and uniform strip forgetting.",
        H("Alternating reset square algebra"),
        Blocks(
            Paragraph(Text("In all displays q:Nat is unbounded, NatPositive(q) means 0 < q, and Sign is the fixed Multiplicative Bool with native XOR addition. Group, Fintype and DecidableEq instances are those of this concrete Sign; there are no additional varying carriers or class hypotheses. Matrix is resetMatrix q and Vertex is Fin q times Sign. product, sum, Equiv, fst, snd and length display the corresponding Lean types, equivalence, projections and List.length. The Lean q binders are implicit in these six declarations; hq is explicit in the first four and implicit in the two strip theorems. Prime display names spell Lean prime suffixes. Every other parameter and hypothesis is displayed below.")),
            Paragraph(Text("B q has reset constructors f(i,h) and advance constructors a(i,h,hi), with i:Fin q, h:Sign and hi:i.val+1<q. R q additionally has the distinct identity constructor d(i,h). sourceB and sourceR are (i,h). targetB and targetR send f to (zero hq, flipSign h), a to (next i hi,h), and targetR sends d to (i,h). Each legal original reset coefficient is exactly one: reset has label ofAdd true, advance has label 1, and both have the unique number zero. No adjacency quotient or edge multiplicity is discarded; the absolute source sign is retained. The additive identity-plus-reset number intervals are refined in the upper ResetAlternatingHistories owner.")),
            Describe.Lean(DescribeId.Create("typed-original-reset-edge-equivalence"),
                DeclarationHandle.Create(Prefix + "actualEdgeEquiv"),
                H("Every original numbered reset edge and absolute sign"),
                StatementSource.FromAuthor(Disp(All(Typed(
                    Call("actualEdgeEquiv", I("hq")), Call("Equiv", BEdges, Edge))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("originalEdge and typedEdge are the two inverse functions, with actual_source and actual_target preserving the expanded graph endpoints. The inverse proofs use the actual matrix support and numbered-edge extensionality, including the coefficient-one number constraint. This equivalence works for every positive q, including q=1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("typed-identity-reset-boundary-equivalence"),
                DeclarationHandle.Create(Prefix + "actualBoundaryEquiv"),
                H("Identity vertices and original numbered reset edges remain distinct"),
                StatementSource.FromAuthor(Disp(All(Typed(
                    Call("actualBoundaryEquiv", I("hq")),
                    Call("Equiv", REdges, Call("sum", Vertex, Edge)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward decoder is originalBoundary and the inverse is typedBoundary. The d constructor enters the identity-vertex summand; f and legal a enter the original numbered B-edge summand via actualEdgeEquiv. This typed sum equivalence composes with the numbered-edge equivalence for the literal matrix identity plus resetMatrix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("left-endpoint-square-operation"),
                DeclarationHandle.Create(Prefix + "leftSquare_spec"),
                H("A compatible left input and terminal boundary determine their square"),
                StatementSource.FromAuthor(Disp(All(For(
                    Square(First(LeftChoice), I("x"), Second(LeftChoice), I("s")),
                    B("x", BEdges), B("s", REdges),
                    B("hc", Equal(TargetB(I("x")), SourceR(I("s")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Square hq r x y s has eight guarded constructors fdSwap, fdFix, afSwap, afFix, ff, fa, ad and aa. The FD/AF swap requires both an available advance i.val+1<q and even i.val; fdFix retains the terminal exception. square_endpoints gives sourceR r=sourceB x, targetR r=sourceB y, targetB x=sourceR s and targetR s=targetB y. The endpointSquare is the constructed equivalence BRFiber hq v z to RBFiber hq v z for every v,z:Vertex: the left fiber retains (x,s), sourceB x=v, targetB x=sourceR s and targetR s=z; the right fiber retains (r,y), sourceR r=v, targetR r=sourceB y and targetB y=z. leftSquare uses its forward map; rightSquare uses its inverse. Existence and both uniqueness proofs construct this equivalence. On incompatible inputs the total operations use their specified identity fallback, so the displayed hc hypothesis is essential. The finite tables and numbered square interface use these operations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-endpoint-square-operation"),
                DeclarationHandle.Create(Prefix + "rightSquare_spec"),
                H("A compatible initial boundary and right input determine their square"),
                StatementSource.FromAuthor(Disp(All(For(
                    Square(I("r"), First(RightChoice), I("y"), Second(RightChoice)),
                    B("r", REdges), B("y", BEdges),
                    B("hc", Equal(TargetR(I("r")), SourceB(I("y")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the inverse endpointSquare operation on the exact same guarded relation. square_right_unique recovers both the input B edge and terminal R boundary from the initial R boundary and right B edge; square_left_unique recovers both the initial boundary and output edge from the left edge and terminal boundary. The operations are used by sweepLeft and sweepRight and their soundness proofs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-q-square-strip-forgetting"),
                DeclarationHandle.Create(Prefix + "strip_left_forgets"),
                H("A common q-edge left strip forces the initial full boundary"),
                StatementSource.FromAuthor(Disp(EvenAll(For(
                    Equal(Boundary(I("r")), Boundary(I("rPrime"))),
                    B("xs", BList), B("ys", BList), B("ysPrime", BList),
                    B("r", REdges), B("rPrime", REdges),
                    B("s", REdges), B("sPrime", REdges),
                    B("hs", Strip(I("xs"), I("r"), I("s"), I("ys"))),
                    B("hsPrime", Strip(I("xs"), I("rPrime"), I("sPrime"), I("ysPrime"))),
                    B("hlen", Equal(Call("length", I("xs")), I("q"))),
                    B("hc", Equal(SourceR(I("s")), SourceR(I("sPrime")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strip is the nil/cons inductive relation retaining all left and right B edges and both R boundaries, with existential internal boundaries in Prop. The lists and boundaries are otherwise unrestricted; the Lean xs,ys,ysPrime,r,rPrime,s,sPrime binders are implicit. leftRank is positive on unequal boundaries with a common source, at most q for even q, and strictly increases from initial to terminal along a common left edge. strip_left_rank sums this increase over the strip. The displayed common terminal source is the only endpoint comparison hypothesis; terminal targets are independent. first_output_independent uses this result on the q-edge tail of a q+1 strip; resetFiniteForgetting later obtains hc from the last common left edge."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-q-square-strip-forgetting"),
                DeclarationHandle.Create(Prefix + "strip_right_forgets"),
                H("A common q-edge right strip forces the terminal full boundary"),
                StatementSource.FromAuthor(Disp(EvenAll(For(
                    Equal(Boundary(I("s")), Boundary(I("sPrime"))),
                    B("xs", BList), B("xsPrime", BList), B("ys", BList),
                    B("r", REdges), B("rPrime", REdges),
                    B("s", REdges), B("sPrime", REdges),
                    B("hs", Strip(I("xs"), I("r"), I("s"), I("ys"))),
                    B("hsPrime", Strip(I("xsPrime"), I("rPrime"), I("sPrime"), I("ys"))),
                    B("hlen", Equal(Call("length", I("ys")), I("q"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Lean xs,xsPrime,ys,r,rPrime,s,sPrime binders are implicit; there is no common-initial-source hypothesis. rightRank is positive on unequal boundaries, bounded by q and strictly decreases from initial to terminal along a common right edge. strip_right_rank sums this decrease and forces the terminal boundaries to agree after q edges. Distinct reset origins are included in the comparison. last_input_independent consumes the q-edge prefix and resetFiniteForgetting consumes arbitrary natural-indexed square strips. Both forgetting statements preserve the full originalBoundary values, hence their typed boundaries by actualBoundaryEquiv.injective. No bounded enumeration of q or words supplies either proof."))),
                DescribeRole.Theorem))));
}
