using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class SharpBinaryOneRecutDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => DefinitionDsl.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Words => Call("List", V("Bool"));
    private static Formula Languages => Call("Set", Words);
    private static Formula Boundaries => Seq(Languages, Sp, Times, Sp, Words);
    private static Formula Residuals(Formula c, Formula k) => Call("residualSet", c, k);
    private static Formula Image(Formula c, Formula k) => Call("image", c, k, Num(1));
    private static Formula Fiber(Formula c, Formula k, Formula e) => Call("currentFiber", c, k, e);
    private static Formula BitFiber(Formula c, Formula k, Formula e, Formula b) =>
        Call("fixedBitFiber", c, k, e, b);
    private static Formula FixedLength(Formula c, Formula n) => All("w", Words,
        Imp(Member(V("w"), c), Equal(Call("length", V("w")), n)));

    private static Formula Bounds(Formula c, Formula k, Formula q)
    {
        var e = V("E"); var b = V("b");
        return And(All("E", Languages, Imp(Member(e, Residuals(c, k)), And(
            Le(Card(Fiber(c, k, e)), Multiply(Num(2), q)),
            All("b", V("Bool"), Le(Card(BitFiber(c, k, e, b)), q))))),
            Le(Card(Image(c, k)), Multiply(Multiply(Num(2), Card(Residuals(c, k))), q)));
    }

    private static Formula Attains(Formula width, bool full)
    {
        var c = Call("relation", width, V(full ? "true" : "false"));
        var k = Add(Multiply(Num(2), width), Num(1));
        var n = Add(Multiply(Num(3), width), Num(1));
        var q = full ? width : Add(width, Num(1));
        var e = V("E"); var b = V("b");
        return And(Call("Nonempty", c), FixedLength(c, n), Le(Num(1), k), Le(k, n),
            Imp(Equal(V(full ? "true" : "false"), V("true")), Call("FullBranching", c, k)),
            Equal(Card(Residuals(c, k)), width),
            Equal(Card(Image(c, k)), Multiply(Multiply(Num(2), width), q)),
            All("E", Languages, Imp(Member(e, Residuals(c, k)), And(
                Equal(Card(Fiber(c, k, e)), Multiply(Num(2), q)),
                All("b", V("Bool"), Equal(Card(BitFiber(c, k, e, b)), q))))));
    }

    private static Formula Statement()
    {
        var n = V("n"); var c = V("C"); var k = V("k"); var z = V("z");
        var r = Residuals(c, k); var width = Card(r); var prescribed = V("N");
        var universal = All("n", V("Nat"), All("C", Languages, All("k", V("Nat"),
            Imp(And(FixedLength(c, n), Call("Nonempty", c), Le(Num(1), k), Le(k, n)),
                And(Call("Finite", r), Lt(Num(0), width),
                    All("z", Boundaries, Imp(Member(z, Image(c, k)), Member(Call("recut", z), r))),
                    Bounds(c, k, Add(width, Num(1))),
                    Imp(Call("FullBranching", c, k), Bounds(c, k, width)))))));
        var sharpness = All("N", V("Nat"), Imp(Le(Num(1), prescribed),
            And(Attains(prescribed, false), Attains(prescribed, true))));
        return And(universal, sharpness);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp local cost of one binary recut depends on the actual forward residual width.",
        H("Sharp Binary One Recut"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("optional-word-length"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/SharpBinaryOneRecut.word_length"),
                H("Length of the optional-index encoding"),
                StatementSource.FromAuthor(Disp(All("N", V("Nat"),
                    All("i", Call("Option", Call("Fin", V("N"))),
                        Equal(Call("length", Call("word", V("i"))), V("N")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N and every optional index i in Option(Fin N), word(i) has length N. The word lists the Boolean tests i=some t in the order t in Fin N; this includes N=0 and the none input. Equal lengths allow cancellation of consecutive encoding blocks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optional-word-injectivity"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/SharpBinaryOneRecut.word_injective"),
                H("Recovery of the optional index"),
                StatementSource.FromAuthor(Disp(All("N", V("Nat"),
                    All("i", Call("Option", Call("Fin", V("N"))),
                        All("j", Call("Option", Call("Fin", V("N"))),
                            Imp(Equal(Call("word", V("i")), Call("word", V("j"))),
                                Equal(V("i"), V("j")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N the complete encoding function on Option(Fin N) is injective. Every some s is detected at coordinate s; none is the all-false word. Consequently an injective two-letter alphabet transport preserves optional-index recovery, and concatenated fixed-length blocks recover a finite derivative table coordinate by coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optional-coordinate-cardinality"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/SharpBinaryOneRecut.spare_card"),
                H("Cardinality of a free derivative coordinate"),
                StatementSource.FromAuthor(Disp(All("N", V("Nat"), All("full", V("Bool"), And(
                    Imp(Equal(V("full"), V("false")),
                        Equal(Card(Call("Spare", V("N"), V("full"))), Add(V("N"), Num(1)))),
                    Imp(Equal(V("full"), V("true")),
                        Equal(Card(Call("Spare", V("N"), V("full"))), V("N")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N and Boolean full, Spare(N,full) consists of i in Option(Fin N) such that full=true implies i is not none. Its cardinality is N plus zero when full=true and N plus one when full=false. This includes N=0 in both regimes and gives the number of choices for each free derivative coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("sharp-binary-one-recut"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/SharpBinaryOneRecut.sharp_binary_one_recut"),
            H("Sharp bounds and simultaneous attainment"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let C be one nonempty set of binary words, all of length n, and fix 1 <= k <= n. Write R_k=residualSet(C,k) for the residual languages of actual extendable prefixes of length k. Write Q=image(C,(k,1)) for the actual anchored boundary image with a tail of length one. These are the original carriers of the strict supplied append and bounded deletion model. No independent choice of a residual and a tail is assumed. The residual carrier is finite and has positive cardinal N, as consequences of the binary fixed-length and nonempty hypotheses.")),
                Paragraph(Text("For z=(S,t) in Q, recut(z)={f: tf belongs to S}. This belongs to R_k, so recut restricts to a lawful map Q to R_k. currentFiber(C,k,E) is exactly {z in Q: recut(z)=E}; fixedBitFiber(C,k,E,b) further requires t=[b]. Thus these subsets count the fibers of that actual-image map, with or without the last bit. FullBranching(C,k) means that for every extendable prefix v of length k-1 and each binary b, vb has a completion in this same C.")),
                Paragraph(Text("The displayed bounds abbreviate no extra assumptions: each current fiber has at most 2(N+1) elements, each fixed-bit fiber at most N+1, and Q at most 2N(N+1). With FullBranching the corresponding numbers are 2N, N, and 2N squared. Earlier residuals contain no empty word, since their prefixes have length k-1<n. An earlier residual is therefore exactly the disjoint union of its two first-bit derivatives. Each derivative is empty or an actual member of R_k. Fixing E and b leaves at most N+1 opposite derivatives. The full branching condition excludes the empty option. This gives injective encodings of each fixed-bit fiber, each current fiber and the complete Q into the corresponding finite carriers.")),
                Paragraph(Text("For every positive N, use J=Option(Fin N). Encode none by the all-false word e(none) of length N and some i by the length-N word true only at coordinate i. This encoding is injective, including the distinction between none and every some i. Set v(i,j)=e(i)e(j). In the unrestricted family use all pairs except (none,none); in the full family require both components to be some. The literal words are v(i,j)b e(some s) exactly when the b-selected component is some s, with false selecting i and true selecting j. relation(N,false) and relation(N,true) denote these two actual word sets.")),
                Paragraph(Text("More explicitly, Spare(N,false) is the full optional index set and Spare(N,true) consists of its nonempty options. Point(N,full)=Fin N times Bool times Spare(N,full). A point (s,b,t) sets the selected component to some s and the opposite component to t; code is its literal word. Conversely every literal legal word has such a point. All codewords have length 3N+1 and the cut is 2N+1. A positive N supplies a point and hence a nonempty source. No separate finiteness or positivity premise is imposed.")),
                Paragraph(Text("At length 2N the actual extendable prefixes are exactly v(i,j) with the stated admissibility condition. Their residuals are precisely the languages S(i,j) consisting of false e(some s) when i=some s and true e(some s) when j=some s. Taking the two derivatives recovers i and j, so these predecessor residuals are injective in the pair. At length 2N+1 every actual prefix is exactly the prefix of a Point, and its residual is the singleton containing e(some s). Both directions follow by splitting a literal source word at its fixed lengths; equal-length prefix cancellation and injectivity of e exclude further prefixes or identifications.")),
                Paragraph(Text("The original fine image Q is exactly the range of fine(s,b,t)=(S(i,j),[b]); each point has the actual state (v(i,j),[b]) and completion e(some s). Exhaustion follows by splitting any actual typed state inside a literal source word. fine is injective. Current residuals are exactly the N distinct singletons {e(some s)}. For each such singleton, its entire current fiber is parametrized bijectively by Bool times Spare, and its fixed-bit fiber by Spare. The unrestricted cardinalities are consequently 2N(N+1), 2(N+1), N+1; the full cardinalities are 2N squared, 2N, N. All fibers attain their bounds simultaneously in one C in each regime, including N=1. In the full family the exhaustive predecessor classification proves both append bits legal at every actual earlier prefix.")),
                Paragraph(Text("The universal quantifiers include k=1 and k=n. In the sharpness clauses, lengths vary with N; attainment for every separately prescribed pair of lengths is not asserted. The behavioral interpretation and supplied-deletion separators are provided by strict_anchored_specialization, with parameter d=1, the same C, and the same cut k. The sharp counting argument is the one in Theorem 4.1 of Recursive relational observation: nonlinear recuts, predecessor context and retained memory; the optional one-hot realization makes its arbitrary positive width explicit. This is an attribution of the argument and its scope, with no literature priority claim over reversible automata or trellis theory."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ObserverMemory/StrictAnchoredBoundary"))]));
}
