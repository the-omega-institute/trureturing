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
            Paragraph(Text("Finite sums, the nonnegative recurrence and countable compact extraction are reused mathematical tools. The construction concerns the stated algebraic comparison model; it supplies no additional physical preparation or measurement assumptions and makes no literature priority claim.")),
            UnitTermApplication())));

    private static DocumentBlock UnitTermApplication()
    {
        var n = F.Id("n"); var j = F.Id("j");
        var s = F.Id("s"); var t = F.Id("t"); var x = F.Id("x");
        var free = Call("Term", Call("Empty"));
        var nine = F.Id("Nine");
        Formula ev(Formula a) => Call("evaluate", Call("nineMarker"), a);
        Formula nm(Formula a) => Call("nineMarker", a);
        Formula nr(Formula k, Formula a) => Call("nineReading", k, a);
        Formula read(Formula k, Formula a) => Call("h", k, a);
        Formula product(Formula a, Formula b) => Call("nineMul", a, b);
        Formula recurrence(Formula k, Formula a, Formula b) => Eqn(
            Add(Add(nr(k, product(a, b)), nr(Add(k, D(1)), product(a, nm(b)))),
                nr(Add(k, D(2)), product(a, nm(nm(b))))), Times(3, nr(k, b)));
        return new DocumentBlock.Section(H("Application: bounded row recurrence on every free unit term"), Blocks(
            Paragraph(Text("C133 Unanchored Marker Bounded Orbits Continuation W, Section 29.1, applies the free-term evaluator to a specified nine-state unital magma. The result is one real function on all natural times and all original free unit terms. The following definitions, parameter correspondence and derivation retain that application of existing results; the finite table normalization and witness packaging introduce no new canonical mathematical declaration or theorem handle.")),
            Paragraph(Text("The original carrier is this module's Term Empty. There are no external source generators. Expr has unit, mark and ordered binary product constructors; Normal and termProduct remove exactly left and right unit factors. All other finite bracketings and every finite marker depth remain. In this section U means termMarker on this original carrier. No associativity, commutativity, marker homomorphism, equation U(1)=1 or identity U^3=I is imposed on original terms. In particular, U^3(1) and 1 remain different normal forms. The finite auxiliary evaluation below is a map out of that carrier, not a replacement of it.")),
            new DocumentBlock.Section(H("Auxiliary states, source parameters and exact readings"), Blocks(
                Paragraph(Text("Nine consists of nine distinct labels e,p,q,b0,b1,b2,c0,c1,c2. To match the source exactly, put omega=exp(2*pi*i/3) and Theta={1,omega,omega^2,-1,-omega,-omega^2}. Source e,p,q map respectively to e,p,q. Our bi denotes the source label b_(omega^i), and our ci denotes its b_(-omega^i), for i=0,1,2. Thus b0,b1,b2 correspond to phases 1,omega,omega^2, while c0,c1,c2 correspond to -1,-omega,-omega^2. The label q here is an object, not the external comparison function q(x)=c(x,1). Define chi(e)=chi(p)=chi(q)=0, chi(bi)=omega^i and chi(ci)=-omega^i.")),
                Paragraph(Text("The full marker table is nineMarker(e)=p, nineMarker(p)=q, nineMarker(q)=e; nineMarker(b0)=b2, nineMarker(b2)=b1, nineMarker(b1)=b0; nineMarker(c0)=c2, nineMarker(c2)=c1, nineMarker(c1)=c0. Equivalently it subtracts one modulo three from each phase index. This is precisely the source U0, since chi(nineMarker(x))=omega^2*chi(x). Its period three is an auxiliary-state identity only.")),
                Paragraph(Text("The following ordered rules define every product nineMul(a,b), with e as both-sided unit. First nineMul(e,b)=b and nineMul(a,e)=a for all nine states. For every a and every i, nineMul(a,bi)=bi and nineMul(a,ci)=ci. For each phase state d in {b0,b1,b2,c0,c1,c2}, nineMul(d,p)=nineMul(d,q)=d. Finally nineMul(p,p)=nineMul(q,p)=c0 and nineMul(p,q)=nineMul(q,q)=b2. The overlapping unit and right-phase rules agree. These cases cover all 81 ordered pairs. For example nineMul(nineMul(p,q),p)=b2 while nineMul(p,nineMul(q,p))=c0, so no associativity is used. Taking one=e and multiplication=nineMul gives a MulOneClass: its only required equations are the two unit rules just specified.")),
                Paragraph(Text("Define nineReading(n,x)=1+Re(omega^n*chi(x)). It depends only on n modulo three. The exact rational readings, ordered by residues n=0,1,2, are: e:(1,1,1), p:(1,1,1), q:(1,1,1); b0:(2,1/2,1/2), b1:(1/2,1/2,2), b2:(1/2,2,1/2); c0:(0,3/2,3/2), c1:(3/2,3/2,0), c2:(3/2,0,3/2). These nine triples specify the reading for every natural n, with exact real rational values and no approximation to a complex root. They are the source H_n under the parameter map above.")),
                Paragraph(Text("Every entry lies in [0,2], and the three unit-orbit labels always read one. The marker table and these triples give the shift identity for all nine states and every n:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("x", nine,
                    Eqn(nr(Add(n, D(1)), nm(x)), nr(n, x))))),
                Paragraph(Text("Here is the complete derivation of the finite recurrence, rather than a sample at bounded term depth. For a right phase state t with chi(t)=zeta, right absorption and the marker rule give omega^k*chi(nineMul(s,nineMarker^k(t)))=omega^k*omega^(2k)*zeta=zeta for k=0,1,2, for every s. Their sum is 3*zeta. For t=e the sum is chi(s)+omega*chi(nineMul(s,p))+omega^2*chi(nineMul(s,q)). It is zero when s=e. For s=p or q it is -omega+omega^4=0. For a phase state s it is (1+omega+omega^2)*chi(s)=0. The cases t=p,q are cyclic rotations of this same weighted sum, multiplied by a nonzero power of omega, and remain zero. These cases exhaust all nine choices of t and every s. Thus the weighted chi sum is always 3*chi(t). Multiply it by omega^n, take real parts and add the three constant ones. This gives, with every summand and its time index retained:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("s", nine, All("t", nine,
                    recurrence(n, s, t))))),
                Paragraph(Text("Equivalently, substitute the 81 ordered products into the three exact reading columns, reducing n,n+1,n+2 modulo three. This finite rational normalization derives the displayed identity inside this application; it is not a new independent canonical theorem.")))),
            new DocumentBlock.Section(H("Unrestricted evaluation and the complete seven clauses"), Blocks(
                Paragraph(Text("Instantiate the original evaluate with this MulOneClass Nine, U=nineMarker and the unique function Empty -> Nine. In the formulas below, evaluate nineMarker t abbreviates RawUnanchoredReplication.evaluate nineMarker (fun a : Empty => nomatch a) t; the omitted empty assignment is fixed once for the entire domain. The original eval_one, eval_mark and eval_product give exactly evaluate nineMarker 1=e, evaluate nineMarker (U t)=nineMarker(evaluate nineMarker t), and evaluate nineMarker (s*t)=nineMul(evaluate nineMarker s,evaluate nineMarker t). These are the existing evaluator's laws, including both unit-reduction cases of termProduct. They apply to every original normal form, with no depth parameter or subsequent extension choice.")),
                Paragraph(Text("The marker law is a semiconjugacy. Function.Semiconj.iterate_right applied to that law yields the following identity for every original t and every natural j; it preserves the original marker iterates before evaluating them:")),
                new DocumentBlock.DisplayFormula(All("j", Nat, All("t", free,
                    Eqn(ev(Iter(U, j, t)), Iter(Call("nineMarker"), j, ev(t)))))),
                Paragraph(Text("For all marked units, take the actual subset S={e,p,q} of Nine. Its closure is explicit: nineMarker(e)=p, nineMarker(p)=q and nineMarker(q)=e all belong to S. Hence Set.MapsTo nineMarker S S holds, and Set.MapsTo.iterate supplies Set.MapsTo (nineMarker^[j]) S S for every natural j. Since e belongs to S, every nineMarker^[j](e) belongs to S and reads one for every n. Combining this with the semiconjugacy identity and eval_one proves the marked-unit clause for every j, not merely j=0,1,2. This uses the existing set-iteration theorem; no new induction result is needed.")),
                Paragraph(Text("Fix a single global function, for every natural n and every original t:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("t", free,
                    Eqn(read(n, t), nr(n, ev(t)))))),
                Paragraph(Text("The first three clauses follow directly from the exact readings and the preceding unit-orbit argument:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("t", free,
                    Both(Leq(D(0), read(n, t)), Leq(read(n, t), D(2)))))),
                new DocumentBlock.DisplayFormula(All("n", Nat, Eqn(read(n, One), D(1)))),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("j", Nat,
                    Eqn(read(n, Iter(U, j, One)), D(1))))),
                Paragraph(Text("For clause four, apply the finite shift identity at the actual state evaluate nineMarker t and use eval_mark:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("t", free,
                    Eqn(read(Add(n, D(1)), Mark(t)), read(n, t))))),
                Paragraph(Text("For clause five, let a=evaluate nineMarker s and b=evaluate nineMarker t for arbitrary original s,t. The three evaluated original terms s*t, s*U(t) and s*U(U(t)) are respectively nineMul(a,b), nineMul(a,nineMarker(b)) and nineMul(a,nineMarker(nineMarker(b))), by eval_product and eval_mark. Evaluate their readings at n,n+1,n+2 respectively and apply the finite identity at these actual a,b. Its right side is 3*nineReading(n,b)=3*h(n,t). Consequently the full recurrence is:")),
                new DocumentBlock.DisplayFormula(All("n", Nat, All("s", free, All("t", free,
                    Eqn(Add(Add(read(n, Mul(s, t)), read(Add(n, D(1)), Mul(s, Mark(t)))),
                        read(Add(n, D(2)), Mul(s, Mark(Mark(t))))), Times(3, read(n, t))))))),
                Paragraph(Text("For the last two clauses keep the specified original composite z=(U1)*(U1), with exactly those two marked-unit factors. Its evaluation is nineMul(p,p)=c0, which is the source b_(-1). The residue-zero reading is therefore zero, whereas the original unit reads one:")),
                new DocumentBlock.DisplayFormula(Eqn(read(D(0), Mul(Mark(One), Mark(One))), D(0))),
                new DocumentBlock.DisplayFormula(All("C", R, Seq(Neg, Sp, Open,
                    Leq(read(D(0), One), Mul(F.Id("C"), read(D(0), Mul(Mark(One), Mark(One))))), Close))),
                Paragraph(Text("Indeed, for each real C the proposed inequality reduces to 1<=C*0=0, which is false. This includes every finite real constant, with no sign restriction. The seven clauses hold simultaneously for this one h, independently quantified over all n,j and all original s,t. Arbitrary finite bracketing is handled by the unrestricted original evaluator. The auxiliary image is finite; the original free carrier is not identified with it, and no unexamined finite-depth tail remains.")))),
            new DocumentBlock.Section(H("Full-relation and realization boundaries"), Blocks(
                Paragraph(Text("The source is C133 Unanchored Marker Bounded Orbits Continuation W, Theorem 29.1 and Proposition 29.2. The mathematical ingredients reused here are this module's original Term, termProduct, termMarker, evaluate, eval_one, eval_mark and eval_product, together with Function.Semiconj.iterate_right and Set.MapsTo.iterate. Literal finite tables, their rational normalization, the evaluation transport and logical witness packaging supply the application. They add no canonical theorem, Describe or truth anchor and make no literature priority claim.")),
                Paragraph(Text("Proposition 29.2 keeps a crucial stronger premise separate. If a complete nonnegative four-variable R model actually contained the auxiliary Nine algebra as a subalgebra preserving its unit, multiplication and marker, then every auxiliary state a would satisfy c(x,a)=q(x) and c(a,x)=r(x) for every external x, where q(x)=c(x,1), r(x)=c(1,x). For a right phase state v, its three marker iterates are phase states and the absorption rules give a*U^k(v)=U^k(v)=1*U^k(v) for k=0,1,2. The source's full-R row-and-column identification argument then gives those equalities. In particular q(x)=1 and c(x,c0)=0, with c0=source b_(-1), cannot coexist under that actual-subalgebra premise.")),
                Paragraph(Text("This application installs no such actual nine-state subalgebra of a full-R model and constructs no external nonnegative four-variable R kernel. Equality of two auxiliary evaluations identifies neither the original terms nor their whole R rows or columns. It licenses no quotient by those fibers. The row recurrence does not supply arbitrary external composite constraints, the source's general external-left-factor constraints, or feasibility of all finite systems for any fixed (lambda,B). It establishes no global Hilbert representation, general full-source classification, or physical realization. Preparation, records, measurements, reference systems, joint operations, time operations and source realizability remain additional contracts. Neither the full quantum representation problem nor its physical contract is settled by this row application."))))));
    }

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
