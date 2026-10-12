using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class SameCutWholeRayBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual square lifts and arbitrary futures at the same integer cut.",
        H("Actual square lifts and arbitrary futures at the same integer cut"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in the corresponding definitions; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("actual-local-square-data"),
                DeclarationHandle.Create(Prefix + "Squares"),
                H("Local squares keep their actual boundary edges"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("recordType", Call("Squares", I("A"), I("Bgraph"), I("R"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("D", I("Type")),
                        B("R", I("Type")),
                        B("A", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("Bgraph", Call("DirectedMultigraph", I("V"), I("D")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A : DirectedMultigraph V E and B : DirectedMultigraph V D share their vertex type; R is an arbitrary actual boundary-edge type. recordType displays the Lean structure. Squares stores source, target, sq, endpoint equations, totalized back and forth operations with composable-input specifications and the two local uniqueness laws, plus actual incoming and outgoing R choices at every vertex. It supplies no global lift or whole-ray claim.")),
                    Paragraph(Text("FiniteForgetting S q is a Prop with positive : 0<q. Its left field quantifies ALL natural-indexed x:E, y,y':D and r,r':R square strips of length q with identical left inputs and concludes r 0=r' 0. Its right field quantifies all x,x':E, y:D and r,r':R strips with identical right inputs and concludes r q=r' q. Opposite rows and other boundaries are unrestricted. No extra endpoint equality is assumed. q-run overlap constructs compatible leftBoundary and rightBoundary at EVERY integer time. FullSquare.boundary k is immediately after edge k, so square k relates boundary(k-1), left k, right k and boundary k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arbitrary-future-exact-preimage"),
                DeclarationHandle.Create(Prefix + "whole_ray_preimage"),
                H("Every full legal right future has the prescribed left-past preimage"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Exists(
                                And(
                                    Member(I("z"), Call("leftRay", I("S"), I("x"), I("n"))),
                                    And(
                                        Equal(Apply(Call("H", I("S"), I("K")), I("z")), I("y")),
                                        Equal(
                                            Call("liftBoundary", I("S"), I("K"), I("z"), I("n")),
                                            Call("value", I("r"))))),
                                B("z", Call("History", I("A")))),
                            B("x", Call("History", I("A"))),
                            B("n", I("Int")),
                            B("r", Call("Out", I("S"), I("x"), I("n"))),
                            B("y", Call("History", I("Bgraph"))),
                            B("hy", Member(I("y"), Call("betaRay", I("S"), I("x"), I("n"), I("r"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("D", I("Type")),
                        B("R", I("Type")),
                        B("A", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("Bgraph", Call("DirectedMultigraph", I("V"), I("D"))),
                        B("S", Call("Squares", I("A"), I("Bgraph"), I("R"))),
                        B("q", I("Nat")),
                        B("K", Call("FiniteForgetting", I("S"), I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("leftRay(S,x,n) is S.ray x n={z | forall k:Int, k<=n implies z k=x k}. Out(S,x,n) is {r:R // S.source r=A.target(x n)}; value(r)=r.val. betaRay(S,x,n,r) fixes the right past produced by S.backEdge x n r.val (n-k).toNat for EVERY k<=n. liftBoundary(S,K,z,n) is (S.leftLift K z).boundary n. H(S,K) is (S.leftLift K x).right, constructed rather than postulated.")),
                    Paragraph(Text("The splice uses the prescribed alpha past backward from the exact boundary r at n, then forthRun consumes the supplied y edge at every time strictly after n. Local square seam laws make both histories legal. Derived full-left uniqueness identifies this full lift with leftLift, proving H z=y AND the exact original boundary r at n. The y binder ranges over all full legal histories in the right ray, not selected representative futures."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-integer-same-cut-full-ray-image"),
                DeclarationHandle.Create(Prefix + "same_cut_full_rays"),
                H("The entire image is a union of full represented rays at the same cut"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call(
                                    "image",
                                    Call("H", I("S"), I("K")),
                                    Call("leftRay", I("S"), I("x"), I("n"))),
                                Call("betaFullRayUnion", I("S"), I("hB"), I("x"), I("n"))),
                            B("x", Call("History", I("A"))),
                            B("n", I("Int"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("D", I("Type")),
                        B("R", I("Type")),
                        B("A", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("Bgraph", Call("DirectedMultigraph", I("V"), I("D"))),
                        B("S", Call("Squares", I("A"), I("Bgraph"), I("R"))),
                        B("q", I("Nat")),
                        B("K", Call("FiniteForgetting", I("S"), I("q"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteD", Call("Fintype", I("D"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hB", Call("Essential", I("Bgraph")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("betaFullRayUnion is the union over r:Out S x n of {y:History B | forall k:Int, k<=n implies y k=(S.betaFull hB x n r) k}. The finite V,D and DecidableEq V instances together with Essential B are precisely the represented-ray hypotheses. betaFull extends the prescribed right past by an actual legal outgoing tail to give one full representative. betaRay_is_whole_ray shows its choice of tail restricts NO future member.")),
                    Paragraph(Text("same_cut_whole_ray_image uses the arbitrary-future reverse inclusion. component_disjoint uses right q-step forgetting on the COMMON LAST q right edges to show distinct R indices give disjoint sets; this is not an appeal to global lift uniqueness. betaFull_endpoint is S.target r.val. Thus negative cuts, every original boundary index, and endpoint multiplicity remain in scope. There is no finiteness assumption on R here; a later finite numbered specialization provides it."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("constructed-square-history-homeomorphism"),
                DeclarationHandle.Create(Prefix + "historyHomeomorph"),
                H("Finite forgetting constructs both inverse continuous maps"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("Homeomorph", Call("History", I("A")), Call("History", I("Bgraph"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("D", I("Type")),
                        B("R", I("Type")),
                        B("A", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("Bgraph", Call("DirectedMultigraph", I("V"), I("D"))),
                        B("S", Call("Squares", I("A"), I("Bgraph"), I("R"))),
                        B("q", I("Nat")),
                        B("K", Call("FiniteForgetting", I("S"), I("q"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E"))),
                        B("topD", Call("TopologicalSpace", I("D"))),
                        B("discreteD", Call("DiscreteTopology", I("D"))),
                        B("topR", Call("TopologicalSpace", I("R"))),
                        B("discreteR", Call("DiscreteTopology", I("R")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formula displays the definition's result type with its complete local-square/FiniteForgetting telescope and TopologicalSpace plus DiscreteTopology instances on E,D,R. No finiteness or Essential graph assumption is needed for this construction. leftLift and rightLift are built by q-step recursion and overlap. full_left_unique and full_right_unique derive uniqueness from the two forgetting fields and prove the two inverse identities of historyEquiv.")),
                    Paragraph(Text("The discrete finite-run functions are continuous; coordinatewise continuity in the native product/subtype topology proves H_continuous and Hinv_continuous. FullSquare.shift and lift uniqueness give H_shift for the original unit shifts. These facts concern the constructed H, not an assumed map with prescribed action support."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-numbered-square-boundaries"),
                DeclarationHandle.Create(Prefix + "NumberedData"),
                H("Bind the local squares to the literal numbered boundary graph"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("recordType", Call("NumberedData", I("M"), I("N"), I("C"))),
                        B("Hgroup", I("Type")),
                        B("groupH", Call("Group", I("Hgroup"))),
                        B("finiteH", Call("Fintype", I("Hgroup"))),
                        B("decH", Call("DecidableEq", I("Hgroup"))),
                        B("a", I("Nat")),
                        B("M", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("N", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("C", Call("GroupMat", I("Hgroup"), I("a"), I("a")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Hgroup is any Group with Fintype and DecidableEq instances; a:Nat is arbitrary, and M,N,C : GroupMat Hgroup a a. recordType displays NumberedData's structure type. NumberedData contains squares : Squares (expandedGraph M) (expandedGraph N) with R=Edge C times Hgroup, and source_exact and target_exact equal its boundary endpoints to the original expandedGraph C endpoints.")),
                    Paragraph(Text("ActualOut T alpha n is {r:Edge C times Hgroup // expandedGraph C.source r=expandedGraph M.target(alpha n)}. It retains the full numbered C edge and its absolute group anchor. outEquiv converts only this endpoint proof to squares.Out, without forgetting labels, numbers or group coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("numbered-all-integer-whole-ray-image"),
                DeclarationHandle.Create(Prefix + "numbered_same_cut_whole_ray_image"),
                H("The actual constructed H preserves the original cut and numbered indices"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call(
                                    "image",
                                    Call("H", Call("squares", I("T")), I("K")),
                                    Call("Cleft", I("T"), I("alpha"), I("n"))),
                                Call("numberedRightRayUnion", I("T"), I("hN"), I("alpha"), I("n"))),
                            B("alpha", Call("History", Call("expandedGraph", I("M")))),
                            B("n", I("Int"))),
                        B("Hgroup", I("Type")),
                        B("groupH", Call("Group", I("Hgroup"))),
                        B("finiteH", Call("Fintype", I("Hgroup"))),
                        B("decH", Call("DecidableEq", I("Hgroup"))),
                        B("a", I("Nat")),
                        B("M", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("N", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("C", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("T", Call("NumberedData", I("M"), I("N"), I("C"))),
                        B("q", I("Nat")),
                        B("K", Call("FiniteForgetting", Call("squares", I("T")), I("q"))),
                        B("hN", Call("Essential", Call("expandedGraph", I("N"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Cleft T alpha n and Cright T beta n fix all integer coordinates k<=n of their full legal histories. numberedBeta(T,hN,alpha,n,r) is T.beta hN alpha n r, the generic betaFull representative after outEquiv. numberedRightRayUnion is the indexed union over r:ActualOut T alpha n of Cright T (numberedBeta r) n. The square map is T.squares.H K, with K : FiniteForgetting T.squares q and its positive q field; Essential(expandedGraph N) supplies represented full rays.")),
                    Paragraph(Text("numbered_beta_endpoint identifies the component endpoint with expandedGraph C.target r.val. numbered_components_disjoint uses the right forgetting field to distinguish EVERY unequal full numbered edge index, even if its endpoint is repeated. This is a genuine same-integer-cut image of entire ray sets."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("numbered-every-legal-future-preimage"),
                DeclarationHandle.Create(Prefix + "numbered_arbitrary_future_preimage"),
                H("Every component member lifts with its exact numbered boundary"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Exists(
                                And(
                                    Member(I("x"), Call("Cleft", I("T"), I("alpha"), I("n"))),
                                    And(
                                        Equal(Apply(Call("H", Call("squares", I("T")), I("K")), I("x")), I("y")),
                                        Equal(
                                            Call(
                                                "liftBoundary",
                                                Call("squares", I("T")),
                                                I("K"),
                                                I("x"),
                                                I("n")),
                                            Call("value", I("r"))))),
                                B("x", Call("History", Call("expandedGraph", I("M"))))),
                            B("alpha", Call("History", Call("expandedGraph", I("M")))),
                            B("n", I("Int")),
                            B("r", Call("ActualOut", I("T"), I("alpha"), I("n"))),
                            B("y", Call("History", Call("expandedGraph", I("N")))),
                            B(
                                "hy",
                                Member(
                                    I("y"),
                                    Call(
                                        "Cright",
                                        I("T"),
                                        Call("numberedBeta", I("T"), I("hN"), I("alpha"), I("n"), I("r")),
                                        I("n"))))),
                        B("Hgroup", I("Type")),
                        B("groupH", Call("Group", I("Hgroup"))),
                        B("finiteH", Call("Fintype", I("Hgroup"))),
                        B("decH", Call("DecidableEq", I("Hgroup"))),
                        B("a", I("Nat")),
                        B("M", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("N", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("C", Call("GroupMat", I("Hgroup"), I("a"), I("a"))),
                        B("T", Call("NumberedData", I("M"), I("N"), I("C"))),
                        B("q", I("Nat")),
                        B("K", Call("FiniteForgetting", Call("squares", I("T")), I("q"))),
                        B("hN", Call("Essential", Call("expandedGraph", I("N"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("liftBoundary(S,K,x,n) is (S.leftLift K x).boundary n and value(r)=r.val. The binder y is an arbitrary full legal history in Cright of the represented component. Forward phi-inverse recursion consumes its entire right future and yields x with the whole original alpha past through n, H x=y, and EXACTLY r.val as boundary at n. This is stronger than containment in a selected finite collection of representatives and is the reverse inclusion consumed by the concrete reset family."))),
                DescribeRole.Theorem))));
}
