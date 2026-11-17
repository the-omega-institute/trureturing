using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233166KingStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-column king strips, complementary-pair fibres and their exact count.",
        H("Literal normalization, zone counting and the formal generating series"),
        Blocks(
            Paragraph(Text("OEIS A233166, revision 8, NAME: Number of n X 6 0..7 arrays with no element x(i,j) adjacent to itself or value 7-x(i,j) horizontally, diagonally, antidiagonally or vertically, top left element zero, and 1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3 appearing before 4 in row major order (unlabelled 8-colorings with no clashing color pairs).")),
            Node("xor-cancel", "Cancellation of a common xor", "xor_cancel",
                "For colours in Fin 4, xor with a fixed left colour is cancellable.", DescribeRole.Theorem),
            Node("xor-nonzero", "Nonzero xor detects unequal colours", "xor_nonzero",
                "Two Fin 4 colours have nonzero xor exactly when they differ.", DescribeRole.Theorem),
            Node("xor-shift", "Translation of xor differences", "xor_shift",
                "The xor of two translated differences is the original difference.", DescribeRole.Theorem),
            Node("xor-right-cancel", "Cancellation of a common right xor", "xor_right_cancel",
                "For Fin 4 colours, applying xor with the same colour twice returns the original colour.", DescribeRole.Theorem),
            Node("offset-ok", "Admissible six-column offsets", "offsetOK",
                "An offset word starts at zero and has no zero adjacent xor increment.", DescribeRole.Definition),
            Node("offset-choices", "Allowed vertical shifts", "offsetChoices",
                "The allowed shifts are the nonzero colours absent from all adjacent offset increments.", DescribeRole.Definition),
            Node("offset-decidable", "Decidability of offset admissibility", "instDecidableOffsetOK",
                "For each six-column offset word, the zero initial offset and all five nonzero adjacent increments are decidable.", DescribeRole.Definition),
            Node("zones-iff", "Zone data through offset choices", "zones_iff",
                "A zone is equivalent to an admissible offset word whose adjacent first-column increments lie in its allowed shift set.", DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("legal"), DeclarationHandle.Create(Prefix + "Legal"),
                H("Literal functions with free boundaries"), StatementSource.FromAuthor(Disp(LegalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both coordinate inequalities in both directions mean absolute difference at most one. The distinctness condition excludes the same cell. The rank is six times the row plus the column, and every earlier-cell inequality is strict. All functions are counted themselves. Colours may be absent; seven has no further precedence condition. The first-cell existential is false at height zero. Fin.val supplies coordinate values."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "a"),
                H("The literal cardinality"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finset.univ ranges over every function on Fin n times Fin 6 into Fin 8. There is no group quotient, orbit divisor, transposition or boundary identification. The zero constant coefficient extends the positive-height source sequence only for its formal generating series."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The complete source conjunction"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("FORMULA: Empirical: a(n) = 192*a(n-1) - 8192*a(n-2) for n>3. Conjectures from _Colin Barker_, Oct 09 2018: (Start) G.f.: 4*x*(59 - 10304*x + 356352*x^2) / ((1 - 64*x)*(1 - 128*x)). a(n) = 64^(n-1) * (2^n+60) for n>1. (End). The first DATA entry is 236. This proposition includes that exceptional value and every universal onset. PowerSeries.mk uses rational casts of the actual counts. X denotes PowerSeries.X over the rationals. The displayed denominator has constant coefficient one, so its formal inverse exists uniquely. The result below proves exactly this conjunction about the literal count."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("proper"), DeclarationHandle.Create(Prefix + "Proper"),
                H("Labelled proper pair-colourings"), StatementSource.FromAuthor(Disp(ProperFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The four labels name the complementary pairs. Proper means different labels at every distinct neighbouring cell pair, with both coordinate differences at most one. No normalization or surjectivity is included in this auxiliary class."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zones"), DeclarationHandle.Create(Prefix + "zones"),
                H("First-column values and first-row offsets"), StatementSource.FromAuthor(Disp(ZonesFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A zone datum z is the pair (u,v) of first-column values and first-row offsets. The offset v(0) is zero. Adjacent increments of each word are nonzero, and each horizontal increment differs from every vertical increment. Bounded natural indices denote their corresponding Fin indices; their proof arguments do not affect values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("equivalence"), DeclarationHandle.Create(Prefix + "zoneEquiv"),
                H("A bijection for every positive height"), StatementSource.FromAuthor(Disp(EquivalenceFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The forward map records u(i)=c(i,0) and v(j)=c(0,0) xor c(0,j). The inverse sends (u,v) to c(i,j)=u(i) xor v(j). The displayed equations describe the underlying functions of the subtype maps; proofs of membership are omitted. The rectangle identity proves the first composite is the identity. The zero offset proves the second. For the converse adjacency proof, equal rows or equal columns use the nonzero increments, and both diagonal directions use the disjointness of horizontal and vertical increments. This bijection includes height one; the later all-four-colours and literal-prefix saturation conclusions require height at least two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rectangle"), DeclarationHandle.Create(Prefix + "pair_rectangle"),
                H("Necessary zone data for every literal strip"), StatementSource.FromAuthor(Disp(RectangleFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Write c(i,j)=beta(f(i,j)), where beta identifies the complementary pairs {0,7}, {1,6}, {2,5}, {3,4}. The binary operation xor is bitwise exclusive-or on Fin 4. Every adjacent square has four distinct pair colours. The xor of its upper edge equals that of its lower edge, and likewise for its left and right edges. Induction along rows and columns gives the displayed reconstruction. Horizontal and vertical increments are nonzero, and every horizontal increment differs from every vertical increment because the antidiagonal cells are adjacent. The first square also contains all four pair colours. Strict precedence then forces the literal colours one, two and three to have appeared within the first two rows. There are two allowed nonzero vertical increments when all five horizontal increments agree, and one otherwise. This is a count of pair increments, not yet a count of signed colour-row continuations. The zone correspondence is the algebraic rectangular form of Eppstein's published kinggraph construction. This statement concerns the original literal functions and does not replace their count with a labelled count."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-pattern-card-four"), DeclarationHandle.Create(Prefix + "canonical_pattern_card4"),
                H("Twenty-four labelings per canonical pattern"), StatementSource.FromAuthor(Disp(CanonicalPatternCardFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The cell type C is arbitrary, finite and linearly ordered. The predicate S is invariant under every permutation of Fin 4, and every pattern satisfying S uses all four labels. Canonical retains the original first-occurrence normalization. Each canonical pattern therefore has exactly twenty-four distinct labelings. The surjectivity hypothesis is essential to the permutation factor; the theorem imposes no rectangle or adjacency hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The complete literal count and formal series"), StatementSource.FromAuthor(Disp(EventFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The theorem proves the complete conjunction defined above. At the first occurrence of each complementary pair, the literal colour is its lower representative. All other positions have independent Boolean signs. The explicit fibre equivalence therefore has size two to the number of cells minus the number of used pair labels. A two-by-two square forces all four labels at heights at least two, giving the exact sign factor 2^(6n-4). Canonical representatives use labels in first-occurrence order. The existing general canonical-representative theorem supplies existence and uniqueness; a bijection with the twenty-four permutations of four labels proves the label factor, using the square's surjectivity. No division is assumed for missing labels.")),
                    Paragraph(Text("For each first-row offset word, vertical words are walks whose permitted xor increments form its available set. The existing general finite-walk counting theorem gives four times the available-set cardinality to the number of vertical steps. Among proper offset words of length six beginning at zero, exactly three have two choices, ninety have one, and one hundred fifty have none. This finite certificate concerns 4^6 pair words; height remains arbitrary. It gives labelled count 4(3 times 2^(n-1)+90) for every n at least two. Combining the two exact fibres yields the displayed literal formula.")),
                    Paragraph(Text("The height-one certificate uses canonical proper pair words and the weight 2^(6-k), where k is the actual number of used labels. It includes absent colours and gives 236. The integer recurrence follows from the two geometric terms 2 times 128^(n-1) and 60 times 64^(n-1). Multiplying the formal series by the denominator proves its coefficient identity, with the exceptional initial coefficients handled separately. The denominator has constant coefficient one, and the formal inverse law gives precisely the claimed rational series."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hardin233166"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(NodeFormula(declaration))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula LegalFormula()
    {
        var n=V("n"); var f=V("f"); var p=V("p"); var q=V("q");
        var cells=Product(Call("Fin",n),Fin(6));
        Formula At(Formula r) => App(f,r);
        Formula Coord(Formula r, string name) => Val(Call(name,r));
        var adjacent=And(Ne(p,q),And(
            Le(Coord(p,"Prod.fst"),Add(Coord(q,"Prod.fst"),D(1))),And(
            Le(Coord(q,"Prod.fst"),Add(Coord(p,"Prod.fst"),D(1))),And(
            Le(Coord(p,"Prod.snd"),Add(Coord(q,"Prod.snd"),D(1))),
            Le(Coord(q,"Prod.snd"),Add(Coord(p,"Prod.snd"),D(1)))))));
        var bonds=All("p",cells,All("q",cells,Imp(adjacent,
            And(Ne(At(p),At(q)),Ne(Add(Val(At(p)),Val(At(q))),D(7))))));
        Formula Earlier(byte k) => Ex("q",cells,And(Lt(Rank(q),Rank(p)),Eq(At(q),D(k))));
        var normal=All("p",cells,And(
            Imp(Or(Eq(At(p),D(2)),Or(Eq(At(p),D(3)),Or(Eq(At(p),D(4)),Or(Eq(At(p),D(5)),Eq(At(p),D(6)))))),Earlier(1)),
            And(Imp(Or(Eq(At(p),D(3)),Or(Eq(At(p),D(4)),Eq(At(p),D(5)))),Earlier(2)),
                Imp(Eq(At(p),D(4)),Earlier(3)))));
        var first=Ex("i",Call("Fin",n),And(Eq(Val(V("i")),D(0)),Eq(At(Pair(V("i"),D(0))),D(0))));
        return All("n",V("Nat"),All("f",Arrow(cells,Fin(8)),
            Iff(Call("Legal",f),And(first,And(bonds,normal)))));
    }

    private static Formula CountFormula()
    {
        var n=V("n"); var f=V("f");
        var pred=Seq(LambdaLower,Sp,f,Colon,Sp,Arrow(Product(Call("Fin",n),Fin(6)),Fin(8)),
            Sp,Mapsto,Sp,Call("Legal",f));
        return All("n",V("Nat"),Eq(Call("a",n),Call("Finset.card",Call("Finset.filter",pred,Call("Finset.univ")))));
    }

    private static Formula CanonicalPatternCardFormula()
    {
        var c = V("C"); var s = V("S"); var p = V("P");
        var word = Arrow(c, Fin(4));
        var invariant = All("e", Call("Equiv.Perm", Fin(4)), All("P", word,
            Iff(App(s, Call("Function.comp", V("e"), p)), App(s, p))));
        var surjective = All("P", word, Imp(App(s, p), Call("Function.Surjective", p)));
        Formula Patterns(Formula predicate) =>
            Seq(OpenBrace, p, Colon, Sp, word, Sp, Vert, Sp, predicate, CloseBrace);
        var count = Eq(Call("Nat.card", Patterns(App(s, p))),
            Mul(D(2,4), Call("Nat.card", Patterns(And(App(s, p), Call("Canonical", p))))));
        return All("C", Name("Type"), Seq(
            OpenBracket, Call("Fintype", c), CloseBracket, Comma, Sp,
            OpenBracket, Call("LinearOrder", c), CloseBracket, Comma, Sp,
            All("S", Arrow(word, Name("Prop")), Imp(invariant, Imp(surjective, count)))));
    }

    private static Formula ClaimFormula() => Iff(Call("claim"), EventFormula());

    private static Formula EventFormula()
    {
        var x=V("X"); var n=V("n");
        Formula A(Formula k) => Call("a",k);
        var series=Call("PowerSeries.mk",Seq(LambdaLower,Sp,n,Colon,Sp,V("Nat"),Sp,Mapsto,Sp,Parenthesized(Seq(A(n),Colon,Sp,V("Rat")))));
        var numerator=Mul(Mul(D(4),x),Add(Sub(D(5,9),Mul(D(1,0,3,0,4),x)),Mul(D(3,5,6,3,5,2),Pow(x,D(2)))));
        var denominator=Mul(Sub(D(1),Mul(D(6,4),x)),Sub(D(1),Mul(D(1,2,8),x)));
        var gf=Seq(Eq(series,Mul(numerator,Pow(denominator,new Formula.Negate(Num(1))))),Sp,Name("in"),Sp,Call("PowerSeries",V("Rat")));
        var closed=All("n",V("Nat"),Imp(Le(D(2),n),Eq(A(n),Mul(Pow(D(6,4),Sub(n,D(1))),Add(Pow(D(2),n),D(6,0))))));
        var recurrence=All("n",V("Nat"),Imp(Le(D(4),n),Eq(Parenthesized(Seq(A(n),Colon,Sp,V("Int"))),
            Sub(Mul(D(1,9,2),Parenthesized(Seq(A(Sub(n,D(1))),Colon,Sp,V("Int")))),Mul(D(8,1,9,2),Parenthesized(Seq(A(Sub(n,D(2))),Colon,Sp,V("Int"))))))));
        return And(Eq(A(D(1)),D(2,3,6)),And(gf,And(closed,recurrence)));
    }

    private static Formula RectangleFormula()
    {
        var n=V("n"); var f=V("f"); var i=V("i"); var j=V("j"); var k=V("k"); var p=V("p");
        Formula C(Formula r, Formula s) => Call("beta",App(f,Pair(r,s)));
        Formula H(Formula s) => Call("xor",C(D(0),Call("Fin.castSucc",s)),C(D(0),Call("Fin.succ",s)));
        Formula T(Formula r) => Call("xor",C(r,D(0)),C(Add(r,D(1)),D(0)));
        var reconstruction=All("i",Call("Fin",n),All("j",Fin(6),Eq(C(i,j),Call("xor",Call("xor",C(i,D(0)),C(D(0),D(0))),C(D(0),j)))));
        var horizontal=All("j",Fin(5),Ne(H(j),D(0)));
        var vertical=All("i",V("Nat"),Imp(Lt(Add(i,D(1)),n),And(Ne(T(i),D(0)),All("j",Fin(5),Ne(H(j),T(i))))));
        var exhaustive=All("k",Fin(4),Ex("p",Product(Call("Fin",n),Fin(6)),And(Le(Val(Call("Prod.fst",p)),D(1)),Eq(Call("beta",App(f,p)),k))));
        var seen=All("d",Fin(3),Ex("p",Product(Call("Fin",n),Fin(6)),And(Le(Val(Call("Prod.fst",p)),D(1)),Eq(Val(App(f,p)),Add(Val(V("d")),D(1))))));
        var w=V("w");
        var available=Call("Finset.card",Call("Finset.filter",Seq(LambdaLower,Sp,w,Colon,Sp,Fin(4),Sp,Mapsto,Sp,
            Parenthesized(And(Ne(w,D(0)),All("j",Fin(5),Ne(H(j),w))))),Call("Finset.univ")));
        var rate=Eq(available,Call("ite",All("j",Fin(5),Eq(H(j),H(D(0)))),D(2),D(1)));
        return All("n",V("Nat"),Imp(Le(D(2),n),All("f",Arrow(Product(Call("Fin",n),Fin(6)),Fin(8)),
            Imp(Call("Legal",f),And(reconstruction,And(horizontal,And(vertical,And(exhaustive,And(seen,rate)))))))));
    }

    private static Formula ProperFormula()
    {
        var n=V("n"); var c=V("c"); var p=V("p"); var q=V("q");
        var cells=Product(Call("Fin",n),Fin(6));
        Formula Co(Formula r,string name) => Val(Call(name,r));
        var near=And(Ne(p,q),And(Le(Co(p,"Prod.fst"),Add(Co(q,"Prod.fst"),D(1))),And(
            Le(Co(q,"Prod.fst"),Add(Co(p,"Prod.fst"),D(1))),And(
            Le(Co(p,"Prod.snd"),Add(Co(q,"Prod.snd"),D(1))),Le(Co(q,"Prod.snd"),Add(Co(p,"Prod.snd"),D(1)))))));
        return All("n",V("Nat"),All("c",Arrow(cells,Fin(4)),Iff(Call("Proper",c),
            All("p",cells,All("q",cells,Imp(near,Ne(App(c,p),App(c,q))))))));
    }

    private static Formula ZonesFormula()
    {
        var n=V("n"); var z=V("z"); var i=V("i"); var j=V("j");
        var u=Call("Prod.fst",z); var v=Call("Prod.snd",z);
        Formula H(Formula t) => Call("xor",App(v,Call("Fin.castSucc",t)),App(v,Call("Fin.succ",t)));
        Formula T(Formula r) => Call("xor",App(u,r),App(u,Add(r,D(1))));
        var pred=And(Eq(App(v,D(0)),D(0)),And(All("j",Fin(5),Ne(H(j),D(0))),
            All("i",V("Nat"),Imp(Lt(Add(i,D(1)),n),And(Ne(T(i),D(0)),All("j",Fin(5),Ne(H(j),T(i))))))));
        return All("n",V("Nat"),All("z",Product(Arrow(Call("Fin",n),Fin(4)),Arrow(Fin(6),Fin(4))),
            Iff(Member(z,Call("zones",n)),pred)));
    }

    private static Formula EquivalenceFormula()
    {
        var n=V("n"); var hn=V("h"); var c=V("c"); var z=V("z"); var i=V("i"); var j=V("j"); var p=V("p");
        var cells=Product(Call("Fin",n),Fin(6)); var equiv=Call("zoneEquiv",hn);
        Formula C(Formula r,Formula t) => App(c,Pair(r,t));
        var u=Seq(LambdaLower,Sp,i,Colon,Sp,Call("Fin",n),Sp,Mapsto,Sp,C(i,D(0)));
        var v=Seq(LambdaLower,Sp,j,Colon,Sp,Fin(6),Sp,Mapsto,Sp,Call("xor",C(D(0),D(0)),C(D(0),j)));
        var forward=All("c",Arrow(cells,Fin(4)),Imp(Call("Proper",c),Eq(Call("Subtype.val",App(equiv,Call("Subtype.mk",c))),Pair(u,v))));
        var result=Seq(LambdaLower,Sp,p,Colon,Sp,cells,Sp,Mapsto,Sp,
            Call("xor",App(Call("Prod.fst",z),Call("Prod.fst",p)),App(Call("Prod.snd",z),Call("Prod.snd",p))));
        var backward=All("z",Product(Arrow(Call("Fin",n),Fin(4)),Arrow(Fin(6),Fin(4))),
            Imp(Member(z,Call("zones",n)),Eq(Call("Subtype.val",App(Call("Equiv.symm",equiv),Call("Subtype.mk",z))),result)));
        var domain=Seq(OpenBrace,c,Colon,Sp,Arrow(cells,Fin(4)),Sp,Slash,Slash,Sp,Call("Proper",c),CloseBrace);
        var codomain=Seq(OpenBrace,z,Colon,Sp,Product(Arrow(Call("Fin",n),Fin(4)),Arrow(Fin(6),Fin(4))),Sp,Slash,Slash,Sp,Member(z,Call("zones",n)),CloseBrace);
        var type=Call("Equiv",domain,codomain);
        return All("n",V("Nat"),All("h",Lt(D(0),n),And(Parenthesized(Seq(equiv,Colon,Sp,type)),And(forward,backward))));
    }

    private static Formula Member(Formula a, Formula b) => Seq(a,Sp,InMacro,Sp,b);

    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Leftrightarrow,Sp,Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Rank(Formula p) => Add(Mul(D(6), Val(Call("Prod.fst", p))), Val(Call("Prod.snd", p)));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));

    private static Formula NodeFormula(string declaration) => declaration switch
    {
        "xor_cancel" => All("a", Call("Fin", Digits("4")), All("b", Call("Fin", Digits("4")), All("c", Call("Fin", Digits("4")), Iff(Eq(Call("Fin.xor", V("a"), V("b")), Call("Fin.xor", V("a"), V("c"))), Eq(V("b"), V("c")))))),
        "xor_nonzero" => All("a", Call("Fin", Digits("4")), All("b", Call("Fin", Digits("4")), Iff(Ne(Call("Fin.xor", V("a"), V("b")), Digits("0")), Ne(V("a"), V("b"))))),
        "xor_shift" => All("a", Call("Fin", Digits("4")), All("b", Call("Fin", Digits("4")), All("c", Call("Fin", Digits("4")), Eq(Call("Fin.xor", Call("Fin.xor", V("a"), V("b")), Call("Fin.xor", V("a"), V("c"))), Call("Fin.xor", V("b"), V("c")))))),
        "xor_right_cancel" => All("x", Call("Fin", Digits("4")), All("d", Call("Fin", Digits("4")), Eq(Call("Fin.xor", V("x"), Call("Fin.xor", V("x"), V("d"))), V("d")))),
        "offsetOK" => All("v", Arrow(Call("Fin", Digits("6")), Call("Fin", Digits("4"))), Iff(Call("offsetOK", V("v")), And(Eq(App(V("v"), Digits("0")), Digits("0")), All("j", Call("Fin", Digits("5")), Ne(Call("Fin.xor", App(V("v"), Call("Fin.castSucc", V("j"))), App(V("v"), Call("Fin.succ", V("j")))), Digits("0")))))),
        "offsetChoices" => All("v", Arrow(Call("Fin", Digits("6")), Call("Fin", Digits("4"))), Eq(Call("offsetChoices", V("v")), Call("Finset.filter", Lam("x", Call("Fin", Digits("4")), And(Ne(V("x"), Digits("0")), All("j", Call("Fin", Digits("5")), Ne(Call("Fin.xor", App(V("v"), Call("Fin.castSucc", V("j"))), App(V("v"), Call("Fin.succ", V("j")))), V("x"))))), Call("Finset.univ")))),
        "instDecidableOffsetOK" => All("v", Arrow(Call("Fin", Digits("6")), Call("Fin", Digits("4"))), Call("Decidable", Call("offsetOK", V("v")))),
        "zones_iff" => All("m", Call("Nat"), All("u", Arrow(Call("Fin", Add(V("m"), Digits("1"))), Call("Fin", Digits("4"))), All("v", Arrow(Call("Fin", Digits("6")), Call("Fin", Digits("4"))), Iff(Member(Pair(V("u"), V("v")), Call("zones", Add(V("m"), Digits("1")))), And(Call("offsetOK", V("v")), All("i", Call("Fin", V("m")), Member(Call("Fin.xor", App(V("u"), Call("Fin.castSucc", V("i"))), App(V("u"), Call("Fin.succ", V("i")))), Call("offsetChoices", V("v"))))))))),
        _ => throw new System.ArgumentOutOfRangeException(nameof(declaration))
    };
    private static Formula Digits(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Lam(string x, Formula t, Formula b) => Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(x), Colon, Sp, t)), Sp, Mapsto, Sp, Parenthesized(b)));
}
