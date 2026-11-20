using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AutomataCircuits;

internal sealed class ExactNFACircuitInfrastructureDocument : IScribeDocumentDefinition
{

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/chen2025lowautomaticcomplexity");
    private static DocumentBlock Node(string name, string id, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact automata, bounded circuit polynomials and finite-grid support estimates.",
        H("Exact automata and circuit obstructions"), Blocks(
            Node("exactlyAccepts", "exactlyaccepts", "Exact acceptance", ExactAcceptance(),
                "Definition 1.1, p. 2: “Let x ∈ Σ∗. An automaton M exactly accepts x if M accepts x, and whenever both y ≠ x and |y| = |x| then M rejects y.” Words are Lists; NFA has no epsilon transitions. Accepting paths need not be unique.",
                AssessedProvenance.FromLiterature(Source)),
            Node("realizesStateCount", "realizesstatecount", "A state-count realization", Realization(),
                "A realization uses Fin k as its state set and a singleton initial-state set. Its accepting-state set is unrestricted.", AssessedProvenance.FromRepo(Source)),
            Node("A_Ne", "a-ne", "Non-deterministic automatic complexity", Minimum(),
                "Definition 1.6, p. 3: “Let x ∈ Σ∗. The non-deterministic automatic complexity of x is Aₙₑ(x) = min{ k ∈ ℕ : there exists an NFA of k states which exactly accepts x }.” A_Ne is the infimum of the displayed natural state counts in ℕ∞; an empty set has infimum infinity.", AssessedProvenance.FromLiterature(Source)),
            Node("Lq", "lq", "The strict threshold language", Threshold(),
                "Definition 1.8, p. 3: “For q ∈ (0,1/2), define Lq = {x ∈ Σ∗ : Aₙₑ(x) < q|x|}.” Length counts original letters. The finite attained state count is coerced into ℚ before comparison.", AssessedProvenance.FromLiterature(Source)),
            Node("Circuit", "circuit", "Finite circuit data", CircuitData(),
                "The four fields describe a finite directed circuit. A gate is a literal, a constant, a finite addition list or a finite multiplication list. The Bool flag negates only input literals.", AssessedProvenance.FromRepo(Source)),
            Node("bounded", "bounded", "Depth and multiplication fan-in", Bounded(),
                "Definition 4.4, p. 16: “Each Ci is defined over the basic set {∧, ⊕} and accepts negative literals.” “The family (Ci)i<ω has constant depth.” “Each Ci has unbounded fan-in-⊕ and bounded fan-in-∧.” “Each Ci accepts words of length i.” Levels strictly increase along every wire; h bounds all levels and b bounds only multiplication input-list lengths.", AssessedProvenance.FromLiterature(Source)),
            Node("evalRounds", "evalrounds", "Synchronous gate evaluation", Rounds(),
                "Round zero is zero at every node. Each following round reads the preceding round at the gate's input nodes. Empty sums and products have values zero and one.", AssessedProvenance.FromRepo(Source)),
            Node("evaluate", "evaluate", "Circuit output", Evaluation(),
                "The output is read after nodes + 1 synchronous rounds. For the acyclic circuits described by bounded this suffices to evaluate every input dependency.", AssessedProvenance.FromRepo(Source)),
            Node("arithmeticRecognizable", "arithmeticrecognizable", "Prime-field recognition on the alphabet", Recognition(false),
                "Arithmetic interpretation, p. 16: “To extend this equivalence beyond binary alphabets, take the field Fₚ for some prime p > 2. By interpreting (⊕, ∧) as (+, ×) mod p, we extend SAC⁰-recognisability to alphabets of prime cardinality.” Here the alphabet is embedded in ZMod p. The bounds h and b precede all lengths. At each length one circuit precedes all input words. Addition fan-in, circuit size and nonuniformity have no bound. Only values on the embedded alphabet are constrained; negative literals evaluate as 1 − Xi.", AssessedProvenance.FromLiterature(Source)),
            Node("booleanRecognizable", "booleanrecognizable", "Recognition of valid Boolean blocks", Recognition(true),
                "Definition 4.4 is interpreted over ZMod 2. One alphabet symbol occupies t bits; the original word has n letters and the circuit has Fin n × Fin t input coordinates. Correctness is imposed on valid encoded words only.", AssessedProvenance.FromLiterature(Source)),
            Node("complexityTotal", "complexitytotal", "Finite attained minima", Totality(),
                "Every word has a finite exact-NFA state minimum and an automaton attaining it.", AssessedProvenance.FromRepo(Source)),
            Node("languageCount", "languagecount", "A length-section cardinality", Count(),
                "Count the length-n words using the bijection between lists of length n and functions Fin n → A.", AssessedProvenance.FromRepo(Source)),
            Node("sparseNonempty", "sparsenonempty", "Finite-scale sparsity with a witness", Sparse(),
                "At each degree D there is a nonempty length section whose cardinality times the alphabet size to the Dth power is strictly below the size of all words of that length.", AssessedProvenance.FromRepo(Source)),
            Node("realizesWordLengthSucc", "realizeswordlengthsucc", "The word-chain realization", ChainBound(),
                "A chain with one state for each prefix, including both endpoints, accepts exactly the given word.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("minimumAttained", "minimumattained", "Attainment of a finite realization minimum", Attainment(),
                "Any nonempty set of realizing natural state counts has a least member, and its coercion equals the infimum used in A_Ne.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("complexityTotalProof", "complexitytotalproof", "Every word has finite exact complexity", TotalProof(),
                "The word-chain realization makes the set of admissible state counts nonempty. Natural-number well-ordering then supplies the minimum.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("memLqMapIff", "memlqmapiff", "Injective alphabet relabelling", Relabel(),
                "Pulling an NFA back along an injection and pushing it forward with no transitions on unused labels preserve exact acceptance and the number of states. Both directions preserve the strict threshold.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("sparseArithmeticNotRecognizable", "sparsearithmeticnotrecognizable", "Sparse arithmetic-language obstruction", ArithmeticObstruction(false),
                "A bounded circuit family has a uniform total-degree bound. Reducing a polynomial on the finite alphabet grid and inducting on a leading coefficient gives a positive support fraction whenever the support is nonempty. This contradicts sparseNonempty.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("sparseArithmeticComplementNotRecognizable", "sparsearithmeticcomplementnotrecognizable", "Complement arithmetic-language obstruction", ArithmeticObstruction(true),
                "Over ZMod p, the polynomial 1 − (P^(p−1)) is nonzero precisely where P vanishes. Its degree is bounded by (p−1) times the original degree. Apply the same sparse-language obstruction.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("sparseBooleanNotRecognizable", "sparsebooleannotrecognizable", "Restriction to two Boolean codewords", BooleanObstruction(false),
                "For each block coordinate the two chosen codewords give an affine polynomial in one Boolean input. Substitution preserves the uniform degree bound, and a sparse nonempty binary pullback contradicts recognition.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("sparseBooleanComplementNotRecognizable", "sparsebooleancomplementnotrecognizable", "The Boolean complement obstruction", BooleanObstruction(true),
                "The same two-codeword restriction applied to the complement is converted by 1 − P over ZMod 2. The original binary pullback supplies the nonempty sparse sections.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static Formula ExactAcceptance()
    {
        var a=X("Alphabet");var k=X("k");var m=X("M");var w=X("w");var y=X("y");
        return All("Alphabet",Ty(),All("k",N(),All("M",Call("NFA",a,FinOf(k)),All("w",ListOf(a),
            Equal(Call("exactlyAccepts",m,w),And(Mem(w,App(Qualified("NFA","accepts"),m)),
                All("y",ListOf(a),Implies(Equal(Len(y),Len(w)),Implies(Mem(y,App(Qualified("NFA","accepts"),m)),Equal(y,w))))))))));
    }
    private static Formula Realization()
    {
        var a=X("Alphabet");var k=X("k");var m=X("M");var w=X("w");var initial=X("initial");
        return All("Alphabet",Ty(),All("w",ListOf(a),All("k",N(),Equal(Call("realizesStateCount",w,k),
            ExistsF("M",Call("NFA",a,FinOf(k)),ExistsF("initial",FinOf(k),
                And(Equal(App(Qualified("NFA","start"),m),Seq(OpenBrace,initial,CloseBrace)),Call("exactlyAccepts",m,w))))))));
    }
    private static Formula Minimum()
    {
        var a=X("Alphabet");var w=X("w");var v=X("v");var k=X("k");
        return All("Alphabet",Ty(),All("w",ListOf(a),Equal(Complexity(w),Call("sInf",
            SetOf("v",InfNat(),ExistsF("k",N(),And(Equal(v,Cast(k,InfNat())),Call("realizesStateCount",w,k))))))));
    }
    private static Formula Threshold()
    {
        var a=X("Alphabet");var w=X("w");var k=X("k");var q=X("q");
        return All("Alphabet",Ty(),All("q",Rat(),Equal(L(a,q),SetOf("w",ListOf(a),
            ExistsF("k",N(),And(Equal(Complexity(w),Cast(k,InfNat())),Less(Cast(k,Rat()),Mul(q,Cast(Len(w),Rat())))))))));
    }
    private static Formula CircuitData()
    {
        var r=X("R");var i=X("I");var nodes=X("nodes");
        return All("R",Ty(),All("I",Ty(),Equal(Call("Circuit",r,i),Seq(OpenBrace,
            X("nodes"),Colon,N(),Semi,Sp,
            X("gate"),Colon,Arrow(FinOf(nodes),Call("Sum",Pair(i,X("Bool")),
                Call("Sum",r,Call("Sum",ListOf(FinOf(nodes)),ListOf(FinOf(nodes)))))),Semi,Sp,
            X("output"),Colon,FinOf(nodes),Semi,Sp,X("level"),Colon,Arrow(FinOf(nodes),N()),CloseBrace))));
    }
    private static Formula Bounded()
    {
        var r=X("R");var i=X("I");var c=X("C");var h=X("h");var b=X("b");var v=X("v");var u=X("u");var inputs=X("inputs");
        var levelV=App(Qualified("Circuit","level"),c,v);var levelU=App(Qualified("Circuit","level"),c,u);
        var wires=All("u",FinOf(App(Qualified("Circuit","nodes"),c)),Implies(Mem(u,inputs),Less(levelU,levelV)));
        var cases=new Formula.Aligned([
            Seq(X("match"),Sp,App(Qualified("Circuit","gate"),c,v),Sp,X("with")),
            Seq(Bar,Sp,App(Qualified("Sum","inl"),X("literal")),Sp,Mapsto,Sp,X("True")),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inl"),X("a"))),Sp,Mapsto,Sp,X("True")),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),App(Qualified("Sum","inl"),inputs))),Sp,Mapsto,Sp,wires),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),inputs))),Sp,Mapsto,Sp,And(LE(Len(inputs),b),wires))]);
        return All("R",Ty(),All("I",Ty(),All("C",Call("Circuit",r,i),All("h",N(),All("b",N(),
            Equal(Call("bounded",c,h,b),All("v",FinOf(App(Qualified("Circuit","nodes"),c)),And(LE(levelV,h),cases))))))));
    }
    private static Formula Rounds()
    {
        var r=X("R");var i=X("I");var c=X("C");var x=X("x");var t=X("t");var v=X("v");var inputs=X("inputs");var index=X("i");var neg=X("negative");
        var prev=Call("evalRounds",c,x,t);
        var cases=new Formula.Aligned([
            Seq(X("match"),Sp,App(Qualified("Circuit","gate"),c,v),Sp,X("with")),
            Seq(Bar,Sp,App(Qualified("Sum","inl"),Parenthesized(Seq(index,Comma,neg))),Sp,Mapsto,Sp,
                X("if"),Sp,neg,Sp,X("then"),Sp,Sub(Num(1),App(x,index)),Sp,X("else"),Sp,App(x,index)),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inl"),X("a"))),Sp,Mapsto,Sp,X("a")),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),App(Qualified("Sum","inl"),inputs))),Sp,Mapsto,Sp,
                App(Qualified("List","sum"),App(Qualified("List","map"),prev,inputs))),
            Seq(Bar,Sp,App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),App(Qualified("Sum","inr"),inputs))),Sp,Mapsto,Sp,
                App(Qualified("List","prod"),App(Qualified("List","map"),prev,inputs)))]);
        return All("R",Ty(),All("I",Ty(),Inst("CommRing",r,All("C",Call("Circuit",r,i),All("x",Arrow(i,r),
            And(All("v",FinOf(App(Qualified("Circuit","nodes"),c)),Equal(Call("evalRounds",c,x,Num(0),v),Num(0))),
                All("t",N(),All("v",FinOf(App(Qualified("Circuit","nodes"),c)),Equal(Call("evalRounds",c,x,Add(t,Num(1)),v),cases)))))))));
    }
    private static Formula Evaluation()
    {
        var r=X("R");var i=X("I");var c=X("C");var x=X("x");
        return All("R",Ty(),All("I",Ty(),Inst("CommRing",r,All("C",Call("Circuit",r,i),All("x",Arrow(i,r),
            Equal(Call("evaluate",c,x),Call("evalRounds",c,x,Add(App(Qualified("Circuit","nodes"),c),Num(1)),App(Qualified("Circuit","output"),c))))))));
    }
    private static Formula Recognition(bool boolean)
    {
        var a=X("Alphabet");var p=X("p");var t=X("t");var e=X("e");var lang=X("L");var h=X("h");var b=X("b");var n=X("n");var c=X("C");var x=X("x");var i=X("i");
        var index=boolean?Pair(FinOf(n),FinOf(t)):FinOf(n);
        var ring=Z(boolean?Num(2):p);
        var input=Lam("i",index,boolean?
            Seq(X("if"),Sp,App(e,App(x,Seq(i,Dot,Num(1))),Seq(i,Dot,Num(2))),Sp,X("then"),Sp,Num(1),Sp,X("else"),Sp,Num(0)):
            App(e,App(x,i)));
        var rhs=ExistsF("h",N(),ExistsF("b",N(),All("n",N(),ExistsF("C",Call("Circuit",ring,index),
            And(Call("bounded",c,h,b),All("x",Arrow(FinOf(n),a),Correct(c,lang,x,input)))))));
        return All("Alphabet",Ty(),All(boolean?"t":"p",N(),All("e",Arrow(a,boolean?Arrow(FinOf(t),X("Bool")):Z(p)),
            All("L",LanguageType(a),Equal(Call(boolean?"booleanRecognizable":"arithmeticRecognizable",boolean?t:p,e,lang),rhs)))));
    }
    private static Formula Totality()
    {
        var a=X("Alphabet");var w=X("w");var k=X("k");
        return All("Alphabet",Ty(),Equal(Call("complexityTotal",a),All("w",ListOf(a),ExistsF("k",N(),
            And(Call("realizesStateCount",w,k),Equal(Complexity(w),Cast(k,InfNat())))))));
    }
    private static Formula Count()
    {
        var a=X("A");var lang=X("L");var n=X("n");var x=X("x");
        return All("A",Ty(),Inst("Fintype",a,All("L",LanguageType(a),All("n",N(),Equal(Call("languageCount",lang,n),
            App(Qualified("Finset","card"),App(Qualified("Finset","filter"),Lam("x",Arrow(FinOf(n),a),Mem(OfFn(x),lang)),Qualified("Finset","univ"))))))));
    }
    private static Formula Sparse()
    {
        var a=X("A");var lang=X("L");var d=X("D");var n=X("n");var x=X("x");
        return All("A",Ty(),Inst("Fintype",a,All("L",LanguageType(a),Equal(Call("sparseNonempty",lang),
            All("D",N(),ExistsF("n",N(),And(ExistsF("x",Arrow(FinOf(n),a),Mem(OfFn(x),lang)),
                Less(Mul(Call("languageCount",lang,n),Pow(Card(a),d)),Pow(Card(a),n)))))))));
    }
    private static Formula ChainBound()
    {
        var a=X("Alphabet");var w=X("w");return All("Alphabet",Ty(),All("w",ListOf(a),Call("realizesStateCount",w,Add(Len(w),Num(1)))));
    }
    private static Formula Attainment()
    {
        var a=X("Alphabet");var w=X("w");var k=X("k");return All("Alphabet",Ty(),All("w",ListOf(a),
            Implies(ExistsF("k",N(),Call("realizesStateCount",w,k)),ExistsF("k",N(),And(Call("realizesStateCount",w,k),Equal(Complexity(w),Cast(k,InfNat())))))));
    }
    private static Formula TotalProof() => All("Alphabet",Ty(),All("w",ListOf(X("Alphabet")),ExistsF("k",N(),
        And(Call("realizesStateCount",X("w"),X("k")),Equal(Complexity(X("w")),Cast(X("k"),InfNat()))))));
    private static Formula Relabel()
    {
        var a=X("A");var b=X("B");var f=X("f");var q=X("q");var w=X("w");return All("A",Ty(),All("B",Ty(),All("f",Arrow(a,b),Implies(Injective(f),All("q",Rat(),All("w",ListOf(a),
            Iff(Mem(App(Qualified("List","map"),f,w),L(b,q)),Mem(w,L(a,q)))))))));
    }
    private static Formula ArithmeticObstruction(bool complement)
    {
        var a=X("A");var lang=X("L");var p=X("p");var e=X("e");return All("A",Ty(),Inst("Fintype",a,
            Implies(LE(Num(2),Card(a)),All("L",LanguageType(a),Implies(Call("sparseNonempty",lang),All("p",N(),
                Implies(App(Qualified("Nat","Prime"),p),All("e",Arrow(a,Z(p)),Implies(Injective(e),
                    Not(Call("arithmeticRecognizable",p,e,complement?Compl(lang):lang)))))))))));
    }
    private static Formula BooleanObstruction(bool complement)
    {
        var a=X("A");var t=X("t");var e=X("e");var lang=X("L");var labels=X("labels");var w=X("w");
        return All("A",Ty(),All("t",N(),All("e",Arrow(a,Arrow(FinOf(t),X("Bool"))),All("L",LanguageType(a),
            All("labels",Arrow(X("Bool"),a),Implies(Call("sparseNonempty",SetOf("w",ListOf(X("Bool")),Mem(App(Qualified("List","map"),labels,w),lang))),
                Not(Call("booleanRecognizable",t,e,complement?Compl(lang):lang))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Ty() => X("Type");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(X(name))) : new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Parenthesized(a), Times, Sp, Parenthesized(b));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsF(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(string cls, Formula type, Formula body) =>
        Seq(OpenBracket, Call(cls, type), CloseBracket, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(X("fun"), Sp, Parenthesized(Seq(X(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, X(name), Colon, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula ListOf(Formula a) => Call("List", a);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Len(Formula w) => App(Qualified("List", "length"), w);
    private static Formula OfFn(Formula x) => App(Qualified("List", "ofFn"), x);
    private static Formula Card(Formula a) => App(Qualified("Fintype", "card"), a);
    private static Formula Compl(Formula a) => new Formula.Power(Parenthesized(a), X("c"));
    private static Formula InfNat() => Call("ENat");
    private static Formula Complexity(Formula w) =>
        App(Seq(Operatorname, Grp(X("A")), Underscore, Grp(X("Ne"))), w);
    private static Formula Z(Formula p) => Call("ZMod", p);
    private static Formula Injective(Formula e) => App(Qualified("Function", "Injective"), e);
    private static Formula L(Formula a, Formula q) =>
        Call("Lq", Seq(X("Alphabet"), Sp, Colon, Eq, Sp, a), q);

    private static Formula LanguageType(Formula a) => Call("Set", ListOf(a));
    private static Formula Correct(Formula c, Formula lang, Formula x, Formula input) =>
        Iff(Mem(OfFn(x), lang), Ne(Call("evaluate", c, input), Num(0)));

}
