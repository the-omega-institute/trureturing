using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawUnanchoredReplicationDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawUnanchoredReplication.";
    private static Formula M => F.Id("M");
    private static Formula U => F.Id("U");
    private static Formula C => F.Id("c");
    private static Formula A => F.Id("A");
    private static Formula N => F.Id("N");
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quot(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula T => Call("Term", A);
    private static Formula One => D(1);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(string x, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Arr(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Open, x, Sp, Rightarrow, Sp, y, Close);
    private static Formula Add(Formula x, Formula y) => Seq(Open, x, Plus, y, Close);
    private static Formula Mul(Formula x, Formula y) => Seq(Open, x, Sp, Cdot, Sp, y, Close);
    private static Formula Times(byte n, Formula x) => Mul(D(n), x);
    private static Formula Cost(Formula x, Formula y) => Call("c", x, y);
    private static Formula Iter(Formula u, Formula n, Formula x) => Call("iterate", u, n, x);
    private static Formula Both(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length - 2; i >= 0; --i)
            r = Seq(Open, xs[i], Sp, Land, Sp, r, Close);
        return r;
    }
    private static Formula Base(Formula body) => All("M", F.Id("Type"),
        Seq(OpenBracket, Call("MulOneClass", M), CloseBracket, Sp,
            All("U", Arr(M, M), All("c", Arr(M, Arr(M, R)), body))));
    private static Formula Raw => Call("RawCost", U, C);
    private static Formula Omega => Call("omega", U, C);
    private static Formula Gamma(Formula a) => Call("gamma", U, N, a);
    private static Formula CN(Formula a, Formula b) => Call("arrayCost", C, N, a, b);
    private static Formula UN => Call("arrayMarker", U);
    private static Formula X(string a) => Call("source", F.Id(a));
    private static Formula Mark(Formula a) => Call("termMarker", a);
    private static Formula DN(Formula s, Formula t) => Call("modelCost", F.Id("f"), U, C,
        Add(Call("rho", F.Id("l")), D(1)), s, t);
    private static Formula Limit(Formula s, Formula t) => Call("Tendsto",
        Seq(LambdaLower, Sp, F.Id("l"), Colon, Sp, Nat, Sp, Mapsto, Sp, DN(s,t)), Call("atTop"),
        Call("nhds", Call("d", s, t)));
    private static Formula Generated()
    {
        Formula p(Formula x) => Call("P", x);
        return All("P", Arr(T, F.Id("Prop")), Imp(Both(p(One),
            All("a", A, p(X("a"))),
            All("s", T, Imp(p(F.Id("s")), p(Mark(F.Id("s"))))),
            All("s", T, All("t", T, Imp(Both(p(F.Id("s")), p(F.Id("t"))),
                p(Mul(F.Id("s"), F.Id("t"))))))), All("s", T, p(F.Id("s")))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal synchronous arrays and countable unit normal forms preserve ordered comparisons while removing unit drift.",
        H("Raw unanchored replication"), Blocks(
            Paragraph(Text("M is an arbitrary genuine unital magma, U is any self-map, and c is finite, real, nonnegative and zero on the diagonal. RawCost requires the full four-variable identity c(au,bv)+c(aUu,bUv)+c(aU(Uu),bU(Uv))=3c(a,b)+3c(u,v). It requires no associativity, commutativity, symmetry, triangle inequality, positivity of a bilinear form, surjectivity of U, or equation U(1)=1.")),
            Entry("raw-synchronous-array-supplier", "raw_replication", "Actual finite-depth supplier", Replication(),
                "Sigma(N) is literally Fin N -> Fin 3. The cost divides the sum over all coordinate arrays by N*3^N. Product and marker act coordinatewise, and the actual unit is the constant old-unit array. The right comb applies a*U^k(inner) at each node. Every source at a coordinate uses the same phase e=(3-s mod 3) mod 3, where s is the sum of that coordinate's phase choices. Thus 3 divides s+e. The corrected old-unit source is U^(s+e)(1), which need not be the actual array unit. The theorem retains every ordered comparison, both actual-unit budgets, the complete raw law and exact unit-budget scaling.", DescribeRole.Theorem),
            Paragraph(Text("The raw recurrence at the two true units is nonnegative, so ThreeWayBalance.nonneg_recurrence_constant supplies synchronous marker isometry. Subtracting consecutive balance laws gives period three for simultaneous right multiplication by unit-orbit markers. Two further balance instances give the unit-orbit budget. These facts provide unit control after phase completion. The synchronous right-comb sum is proved by induction over the literal coordinate arrays, preserving multiplicity, bracketing and order.")),
            Entry("normal-form-uniform-budgets", "normal_form_budgets", "Uniform budgets on actual unit normal forms", Budgets(),
                "The same budget controls all actual evaluation depths. Smart multiplication first removes a unit factor; nonnegativity then gives B(st)<=3(B(s)+B(t)) even in those reduced cases. At a nonunit product the equality follows from the ordered constructor. These bounds supply the compact intervals used by the common all-pair extraction.", DescribeRole.Theorem),
            Entry("raw-zero-drift-realization", "raw_zero_drift", "A common limit on the free unital U terms", ZeroDrift(),
                "A is any finite type of labels, and f maps those labels to the original magma; repetitions and the old unit are allowed. Expr has separate constructors for unit, source, unary marker and ordered binary product. Term is the subset of unit normal forms: a product has two nonunit normal children. Multiplication removes a unit factor and otherwise keeps the binary product constructor. U(unit) is retained. Evaluation into every actual array model respects these operations. Consequently only the two-sided unit laws are imposed; no original operation-preserving or unit-preserving embedding is asserted.", DescribeRole.Theorem),
            Paragraph(Text("For a source a the budget is 3(c(f(a),1)+c(1,f(a)))+6 omega. Unit has budget zero, a marker node has budget 9B+24 omega, and a nonunit product has budget 3(B(s)+B(t)). For every N>=1 the two unit comparisons of an evaluated term sum to at most its budget, and each ordered pair costs at most 3(B(s)+B(t)). All term pairs form one countable index type. The compact product of their finite closed intervals yields a single strictly increasing subsequence, rather than separate choices for separate pairs. All finite scalar balance identities pass to that same limit. Exact omega/N scaling gives zero unit drift, and the source matrix remains exact. The final induction principle states that the actual unit, source symbols, marker and binary product generate every element of Term. Each source symbol differs from the new unit, even if its original label equals the old unit.")),
            Paragraph(Text("Finite sums, the nonnegative recurrence and countable compact extraction are reused mathematical tools. The construction concerns the stated algebraic comparison model; it supplies no additional physical preparation or measurement assumptions and makes no literature priority claim.")))));

    private static Formula Replication()
    {
        var a=F.Id("a"); var b=F.Id("b"); var x=F.Id("x"); var n=F.Id("n");
        Formula frac=Quot(Times(3,Omega),N);
        return Base(Imp(Raw, All("N",Nat,Imp(Seq(D(0),Sp,Lt,Sp,N),Both(
            Call("RawCost",UN,Call("arrayCost",C,N)),
            Eqn(Call("omega",UN,Call("arrayCost",C,N)),Quot(Omega,N)),
            All("a",M,All("b",M,Eqn(CN(Gamma(a),Gamma(b)),Cost(a,b)))),
            All("a",M,Both(Leq(CN(Gamma(a),One),Add(Times(3,Cost(a,One)),frac)),
                Leq(CN(One,Gamma(a)),Add(Times(3,Cost(One,a)),frac)))),
            All("x",M,All("n",Nat,Leq(Add(Cost(Iter(U,n,x),One),Cost(One,Iter(U,n,x))),
                Add(Times(9,Add(Cost(x,One),Cost(One,x))),Mul(D(2,4),Omega))))))))));
    }
    private static Formula Budgets()
    {
        Formula b(Formula s) => Call("budget",F.Id("f"),U,C,s);
        Formula m(Formula s,Formula t) => Call("modelCost",F.Id("f"),U,C,N,s,t);
        var s=F.Id("s"); var t=F.Id("t"); var a=F.Id("a");
        return Base(All("A",F.Id("Type"),All("f",Arr(A,M),Imp(Raw,Both(
            Eqn(b(One),D(0)),
            All("a",A,Eqn(b(X("a")),Add(Times(3,Add(Cost(Call("f",a),One),
                Cost(One,Call("f",a)))),Times(6,Omega)))),
            All("s",T,Eqn(b(Mark(s)),Add(Times(9,b(s)),Mul(D(2,4),Omega)))),
            All("s",T,All("t",T,Leq(b(Mul(s,t)),Times(3,Add(b(s),b(t)))))),
            All("N",Nat,Imp(Seq(D(0),Sp,Lt,Sp,N),All("s",T,All("t",T,Both(
                Leq(Add(m(s,One),m(One,s)),b(s)),
                Leq(m(s,t),Times(3,Add(b(s),b(t))))))))))))));
    }
    private static Formula ZeroDrift() => Base(All("A",F.Id("Type"),
        Seq(OpenBracket,Call("Finite",A),CloseBracket,Sp,
            All("f",Arr(A,M),Imp(Raw,Ex("d",Arr(T,Arr(T,R)),Ex("rho",Arr(Nat,Nat),Both(
                Call("StrictMono",F.Id("rho")),
                All("s",T,All("t",T,Limit(F.Id("s"),F.Id("t")))),
                Call("RawCost",Call("termMarker"),F.Id("d")),
                Eqn(Call("omega",Call("termMarker"),F.Id("d")),D(0)),
                All("a",A,All("b",A,Eqn(Call("d",X("a"),X("b")),
                    Cost(Call("f",F.Id("a")),Call("f",F.Id("b")))))),
                All("a",A,Seq(X("a"),Sp,Neq,Sp,One)),
                Seq(Mark(One),Sp,Neq,Sp,One),Generated()))))))));
    private static DocumentBlock Entry(string id,string name,string title,Formula formula,
        string text,DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Gid+name),H(title),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
}
