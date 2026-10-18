using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SequentialOccupationHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual occupation transitions prepare the uniform word state, and every exact finite chain factors its cut matrix through its actual memory.",
        H("Sequential Occupation History"),
        Blocks(
            Paragraph(Text(
                "A is an alphabet; each statement records its finiteness and decidable-equality assumptions. "
                + "a is a multiset of symbols, t and n are natural numbers, and Word(A,n) is Fin n to A. "
                + "B(a,t) is the existing Boundary subtype: val(b)<=a and card(val(b))=t. "
                + "Subtraction of multisets removes occupation counts. M(n,r) counts actual words "
                + "with occupation r; V(n,r,w) is the existing sectorVector, equal to the complex "
                + "inverse of sqrt(M(n,r)) on legal words and zero elsewhere.")),
            Paragraph(Text(
                "S(a,t) denotes nextStep, a complex matrix with rows (i,c) in A x B(a,t+1) "
                + "and columns b in B(a,t). Its entry is sqrt(count(a-val(b),i)/(card(a)-t)) "
                + "when val(c)=val(b)+{i}, and zero otherwise. The subtraction card(a)-t is in "
                + "natural numbers, and numerator and denominator are included in the reals "
                + "before division. The nonnegative real square root is then included in C. "
                + "Dagger denotes conjugate transpose, and 1 denotes the identity matrix.")),
            Describe.Lean(DescribeId.Create("occupation-sector-head"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sector_head"),
                H("The first symbol separates a normalized occupation vector"),
                StatementSource.FromAuthor(Disp(SectorHead())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/raveh2024dicke")),
                Blocks(Paragraph(Text("A normalized occupation amplitude factors into the square root of the first-symbol frequency and the amplitude for the remaining occupation. The amplitude vanishes when the first symbol is absent."))), DescribeRole.Theorem),
            Theorem("occupation-extension", "extension_exists_iff", "Legal extensions are exactly positive remaining counts",
                Discrete(All("a", Multi, All("t", N, All("b", B(t), All("i", Id("A"),
                    Iff(Exists("c", B(Add(t, D(1))),
                            Eq(Val(Id("c")), Add(Val(b), Call("singleton", Id("i"))))),
                        Lt(Call("count", Val(b), Id("i")), Call("count", a, Id("i"))))))))),
                "The extension is an actual member of the next occupation carrier. This criterion "
                + "does not need finiteness of the alphabet or an active-step hypothesis."),
            Theorem("occupation-step-gram", "next_step_gram", "Every active step has identity Gram matrix",
                Parameters(Imp(Active, Eq(Mul(Dagger(S), S), D(1)))),
                "The columns have unit norm and are mutually orthogonal. Different prefixes cannot "
                + "reach the same next occupation after emitting the same symbol. Summing all "
                + "remaining symbol counts gives card(a)-t, which is positive on an active step."),
            Theorem("occupation-step-channel", "next_step_quantum_channel", "The step induces the canonical quantum channel",
                Parameters(Imp(Active, Exists("channel", Call("QuantumChannel", B(t), Output),
                    All("rho", Call("Matrix", B(t), B(t), C),
                        Eq(Call("toMatrix", Call("toCompletelyPositiveMap", Id("channel"),
                                Call("ofMatrix", Id("rho")))),
                            Mul(Mul(S, Id("rho")), Dagger(S))))))),
                "QuantumChannel is FiniteStateChannel.QuantumChannel. ofMatrix is CStarMatrix.ofMatrix "
                + "and toMatrix is its inverse. The singleton Unit Kraus family uses the frozen "
                + "finite_kraus_quantum_channel theorem; the action holds on every complex input matrix."),
            Paragraph(Text(
                "F(a,n,t,w,b) denotes contraction. For n=0 it is 1 when val(b)=a and 0 otherwise. "
                + "For n+1 it is the finite sum over c in B(a,t+1) of S(a,t)((w(0),c),b) times "
                + "F(a,n,t+1,Fin.tail(w),c). Thus it multiplies and sums the actual step entries "
                + "and caps the final memory by the total-occupation basis vector. The initial "
                + "memory b0(a) is initialBoundary, whose multiset value is empty.")),
            Theorem("occupation-suffix-contraction", "contraction_eq_sector", "Every remaining contraction is the normalized suffix state",
                Parameters(All("n", N, Imp(Eq(Card(a), Add(t, n)),
                    All("w", Word(n), All("b", B(t),
                        Eq(Call("F", a, n, t, w, b), V(n, Sub(a, Val(b)), w))))))),
                "The proof follows the unique legal occupation path and uses the actual word-count "
                + "erasure recurrence for its conditional amplitude. Illegal words give zero. "
                + "No orthogonality, normalization, or exact-preparation premise is assumed."),
            Theorem("occupation-history-preparation", "history_sequential_preparation", "Sequential contraction prepares the actual uniform history",
                Alphabet(All("a", Multi, All("w", Word(Card(a)),
                    Eq(Call("F", a, Card(a), D(0), w, Call("b0", a)), V(Card(a), a, w))))),
                "This includes the empty alphabet and zero time. At the final time the only "
                + "feasible occupation is a. The result is an exact equality at every actual word "
                + "of the original fixed output length."),
            Theorem("occupation-factor-bond-bound", "coefficient_rank_le_bond", "A cut factorization bounds rank by its bond size",
                Parameters(All("s", N, All("beta", Id("Type"), Imp(Call("Fintype", Id("beta")),
                    All("P", Call("Matrix", Word(t), Id("beta"), C),
                        All("Q", Call("Matrix", Id("beta"), Word(Id("s")), C),
                            Imp(Eq(Call("coefficientMatrix", a, t, Id("s")), Mul(Id("P"), Id("Q"))),
                                Le(Call("rank", Call("coefficientMatrix", a, t, Id("s"))),
                                    Call("FintypeCard", Id("beta")))))))))),
                "This companion applies Matrix.rank_mul_le_left and rank_le_card_width. Its "
                + "factorization premise must be established for any proposed sequential "
                + "representation before using it as a memory lower bound."),
            Paragraph(Text(
                "FiniteChain(A,beta) is an actual finite linear chain starting in beta. A terminal "
                + "constructor stores a covector beta to C. A step stores an arbitrary finite next "
                + "carrier gamma, a transition A to Matrix(beta,gamma,C), and a remaining chain "
                + "starting in gamma. Each step emits one symbol. length(c) counts steps; "
                + "cutBond(c,t) is the actual memory after t steps. All carriers may differ; "
                + "they need not be nonempty or have a common dimension. No isometry or physical "
                + "normalization is required of a general chain. Function(X,Y) means maps X to Y.")),
            Paragraph(Text(
                "K(c,v,i) denotes FiniteChain.contract on a list v and initial basis index i. "
                + "For a terminal chain on the empty list it is the terminal covector at i. "
                + "For a step with transition T and remaining chain r on x::xs it is the sum "
                + "over j in the actual next carrier of T(x,i,j) K(r,xs,j). Other constructor/list "
                + "length mismatches give zero. L(c,t,u,i,b) denotes left: at t=0 it is delta(i,b), "
                + "and for a step chain at cut t+1 on x::xs it sums T(x,i,j) L(r,t,xs,j,b). R(c,t,v,b) denotes right: "
                + "it drops t step constructors and contracts v from b with the remaining cap. "
                + "Only cuts t<=length(c) are asserted below. List append is written append; "
                + "wordAppend denotes Fin.append on the existing Fin-indexed words, and ofFn lists their entries.")),
            Theorem("actual-chain-split", "chain_contract_append", "Actual contraction splits through every cut memory",
                ChainParameters(All("t", N, Imp(Le(t, Call("length", c)),
                    All("u", Call("List", Id("A")), All("v", Call("List", Id("A")),
                        Imp(Eq(Call("length", Id("u")), t), All("i", beta,
                            Eq(Call("K", c, Call("append", Id("u"), Id("v")), Id("i")),
                                SumAt("b", Cut(c, t), Mul(
                                    Call("L", c, t, Id("u"), Id("i"), b),
                                    Call("R", c, t, Id("v"), b))))))))))),
                "Induction on the cut, generalized over the starting carrier and prefix, derives "
                + "this identity from the actual recursive sums. The successor step exchanges the "
                + "next-memory and cut-memory sums; the zero cut uses the delta identity. "
                + "The suffix list is unrestricted, so incompatible lengths are also handled."),
            Paragraph(Text(
                "amp(c,initial,w) denotes amplitude, the sum of initial(i) K(c,ofFn(w),i) over i. "
                + "P(c,initial,t) denotes prefixMatrix with entry P(u,b) equal to the sum of "
                + "initial(i) L(c,t,ofFn(u),i,b). Q(c,t,s) denotes suffixMatrix with entry "
                + "Q(b,v)=R(c,t,ofFn(v),b). Their row and column types are respectively "
                + "Word(A,t) x cutBond(c,t) and cutBond(c,t) x Word(A,s). entry(M,u,v) is M(u,v).")),
            Theorem("actual-chain-word-split", "chain_amplitude_append", "The word amplitude is the product entry",
                ChainParameters(All("initial", Call("Function", beta, C), All("t", N, All("s", N,
                    Imp(Le(t, Call("length", c)), All("u", Word(t), All("v", Word(s),
                        Eq(Call("amp", c, initial, Call("wordAppend", Id("u"), Id("v"))),
                            Call("entry", Mul(P, Q), Id("u"), Id("v")))))))))),
                "List.ofFn_fin_append connects the existing actual word concatenation to the "
                + "proved contraction split. Summing the initial vector and exchanging the two "
                + "finite sums gives exactly matrix multiplication at every pair of words."),
            Theorem("actual-sequential-factorization", "sequential_coefficient_factorization", "Every exact chain factors the existing coefficient matrix",
                ExactChainParameters(Imp(FixedLength, Imp(ExactOutput,
                    Eq(Call("coefficientMatrix", a, t, s), Mul(P, Q))))),
                "Exactness quantifies over every full word and equates the computed amplitude "
                + "with sectorVector. It assumes no cut factorization. The existing definition "
                + "of coefficientMatrix on Fin.append and the proved product entries establish "
                + "the matrix equality. The chain has the explicit fixed length t+s."),
            Theorem("actual-sequential-rank", "sequential_rank_necessity", "Every exact chain has a sufficiently large actual cut bond",
                ExactChainParameters(Imp(FixedLength, Imp(ExactOutput,
                    Le(Call("rank", Call("coefficientMatrix", a, t, s)),
                        Call("FintypeCard", Cut(c, t)))))),
                "The preceding constructed factorization supplies the equality premise of "
                + "coefficient_rank_le_bond. The bound uses the cardinality of this chain's actual "
                + "cut carrier, for every finite model satisfying the stated output equality."),
            Theorem("actual-sequential-memory", "sequential_memory_necessity", "The necessary memory is at least the feasible occupation count",
                ExactChainParameters(Imp(Eq(Card(a), Add(t, s)), Imp(FixedLength, Imp(ExactOutput,
                    Le(Card(Call("boundaries", a, t)), Call("FintypeCard", Cut(c, t))))))),
                "The explicit occupation-cardinality condition permits coefficient_rank to "
                + "identify the coefficient rank with the number of feasible boundaries. "
                + "No rank equality or factorization is requested from the proposed model."),
            Paragraph(Text(
                "O(a,n,t) denotes occupationChain. For O(a,n+1,t), the transition is "
                + "T(i,b,c)=S(a,t)((i,c),b) and the remaining chain is O(a,n,t+1). Its zero-step "
                + "terminal covector is delta(val(b),a). I0(a) denotes occupationInitial, the "
                + "delta at initialBoundary(a). Thus this is the already proved occupation "
                + "construction in the general finite-chain carrier.")),
            Theorem("occupation-chain-length", "occupation_chain_length", "The occupation chain has its declared number of steps",
                Discrete(All("a", Multi, All("n", N, All("t", N,
                    Eq(Call("length", O(n, t)), n))))),
                "This structural identity holds for all n and t; the alphabet need only have "
                + "decidable equality."),
            Theorem("occupation-chain-bond", "occupation_chain_bond_card", "Every occupation chain cut has the actual boundary size",
                Discrete(All("a", Multi, All("n", N, All("t", N, All("k", N,
                    Imp(Le(Id("k"), n), Eq(Call("FintypeCard", Cut(O(n, t), Id("k"))),
                        Card(Call("boundaries", a, Add(t, Id("k"))))))))))),
                "Induction selects the stored carrier at the requested legal cut. This counts "
                + "the actual dependent memory type, including empty carriers when the "
                + "occupation constraints have no solution."),
            Theorem("occupation-chain-contraction", "occupation_chain_contract", "The generic chain computes the existing occupation contraction",
                Discrete(All("a", Multi, All("n", N, All("t", N, All("w", Word(n), All("b", B(t),
                    Eq(Call("K", O(n, t), Call("ofFn", w), b), Call("F", a, n, t, w, b)))))))),
                "The recursive finite sums agree at every word and every starting occupation. "
                + "No cardinality or active-step hypothesis is needed for this identification."),
            Theorem("occupation-chain-preparation", "occupation_chain_preparation", "The actual occupation chain is an exact model",
                Alphabet(All("a", Multi, All("w", Word(Card(a)),
                    Eq(Call("amp", O(Card(a), D(0)), Call("I0", a), w), V(Card(a), a, w))))),
                "The initial delta selects the existing history_sequential_preparation theorem. "
                + "The exactness premise of the universal chain theorems is therefore realized "
                + "by the proved occupation construction, including length zero."),
            Theorem("actual-chain-maximum-bond", "maximumBond", "Maximum of the actual chain bonds",
                ChainParameters(Eq(Call("maximumBond", c),
                    SupAt(Add(Call("length", c), D(1)), Call("FintypeCard", Cut(c, t))))),
                "FinsetSup(range(length(c)+1),f) includes every cut from zero through length(c). "
                + "In particular a zero-step chain still has its actual initial/terminal bond.",
                DescribeRole.Definition),
            Theorem("actual-chain-maximum-necessity", "maximum_bond_necessity", "Every exact chain needs the target maximum bond",
                MaximumChainParameters(Imp(Eq(Call("length", c), Card(a)),
                    Imp(ExactWholeOutput, Le(Call("boundaryMaximum", a), Call("maximumBond", c))))),
                "The starting finite type may lie in any universe, independent of the alphabet. "
                + "Every legal cut uses sequential_memory_necessity with remaining length card(a)-t. "
                + "No factorization, isometry, normalized cap, or attaining chain is assumed."),
            Theorem("occupation-chain-maximum", "occupation_chain_maximum_bond", "The occupation chain attains the target maximum",
                Discrete(All("a", Multi,
                    Eq(Call("maximumBond", O(Card(a), D(0))), Call("boundaryMaximum", a)))),
                "occupation_chain_bond_card identifies every actual carrier in the same finite "
                + "supremum, and occupation_chain_length identifies the endpoint."),
            Theorem("actual-achievable-maximum-bonds", "achievableMaximumBonds", "Achievable maximum bonds include actual exact preparations",
                Alphabet(All("a", Multi, All("m", N,
                    Iff(Member(Id("m"), Call("achievableMaximumBonds", a)), AchievableWitness)))),
                "The existential beta ranges over types in the alphabet's universe. Its finite "
                + "instance, chain, initial vector, length equality, pointwise exact output, and "
                + "actual maximumBond value are all part of the witness. The universal necessity "
                + "theorem also applies to carriers in any other universe.", DescribeRole.Definition),
            Theorem("attained-minimum-maximum-bond", "minimum_maximum_bond_characterization", "The least achievable maximum is attained",
                Alphabet(All("a", Multi,
                    Call("IsLeast", Call("achievableMaximumBonds", a), Call("boundaryMaximum", a)))),
                "IsLeast includes membership and a lower bound for every member. Membership "
                + "is witnessed here by beta=B(a,0), occupationChain(a,card(a),0), and the actual "
                + "occupationInitial delta. occupation_chain_preparation supplies the exact "
                + "output, and the previous theorem supplies its maximum. This holds also for "
                + "empty occupation and the empty alphabet."),
            Theorem("history-5040-minimum-maximum-bond", "history_5040_minimum_maximum_bond", "The concrete attained minimum is twelve",
                Call("IsLeast", Call("achievableMaximumBonds", Ast), D(1, 2)),
                "ast is the existing occupation5040 on Option(Fin(3)), with actual counts (4;2,1,1). "
                + "This specializes the general attained theorem using the transported landed maximum."),
            Theorem("history-5040-occupation-attainment", "history_5040_occupation_chain_attainment", "An actual eight-step preparation attains twelve",
                And(Eq(Call("length", ConcreteChain), D(8)),
                    And(Eq(Call("maximumBond", ConcreteChain), D(1, 2)),
                        All("w", Call("Word", Call("Option", Call("Fin", D(3))), Card(Ast)),
                            Eq(Call("amp", ConcreteChain, Call("I0", Ast), w), V(Card(Ast), Ast, w))))),
                "ConcreteChain is O(ast,card(ast),0). The actual initial carrier is Boundary(ast,0), "
                + "with its empty-occupation delta, and the terminal cap selects ast in the full "
                + "boundary carrier. Both have one element. Every full word has exactly the "
                + "target amplitude, and card(ast)=8."),
            Paragraph(Text(
                "The necessity theorem concerns arbitrary algebraic FiniteChains with complex caps. "
                + "The attaining occupation construction additionally has the active-step identity "
                + "Gram matrices and canonical quantum channels proved above. This establishes "
                + "the source's finite MPS and variable-bond sequential-isometry scope. A unitary "
                + "implementation on one fixed twelve-dimensional physical register would also "
                + "need compatible embeddings and unitary extensions; those are not constructed. "
                + "No time-homogeneous prediction-memory claim, or identification with dimension "
                + "sixteen from the different prediction model, follows. These are known Dicke-state "
                + "constructions from Raveh and Nepomechie, with no novelty claim.")))));

    private static Formula SectorHead()
    {
        Formula alpha = Id("A"), r = Id("r"), nn = Id("n"), ww = Id("w");
        Formula wzero = new Formula.Apply(ww, [D(0)]);
        Formula tail = QualifiedHead("Fin", "tail", ww);
        Formula erased = QualifiedHead("Multiset", "erase", r, wzero);
        Formula frequency = new Formula.Fraction(
            Parenthesized(Seq(QualifiedHead("Multiset", "count", wzero, r), Colon,
                Seq(Mathbb, Grp(Id("R"))))),
            Parenthesized(Seq(Parenthesized(Seq(Add(nn, D(1)), Colon, N)), Colon, Seq(Mathbb, Grp(Id("R"))))));
        Formula coefficient = Parenthesized(Seq(QualifiedHead("Real", "sqrt", frequency), Colon, C));
        Formula sector(Formula length, Formula occupation, Formula word) =>
            QualifiedHead("D5.S3.Quantum.Entanglement.OccupancyWordSectors", "sectorVector",
                length, occupation, word);
        Formula rhs = Seq(Operatorname, Grp(Id("if")), Sp, Parenthesized(Member(wzero, r)),
            Sp, Operatorname, Grp(Id("then")), Sp,
            Mul(coefficient, sector(nn, erased, tail)), Sp,
            Operatorname, Grp(Id("else")), Sp, D(0));
        return All("A", Id("Type"), Seq(
            OpenBracket, Call("Fintype", alpha), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", alpha), CloseBracket, Sp,
            All("r", Call("Multiset", alpha), All("n", N,
                Imp(Eq(QualifiedHead("Multiset", "card", r), Add(nn, D(1))),
                    All("w", new Formula.TypeArrow(Call("Fin", Add(nn, D(1))), alpha),
                        Eq(sector(Add(nn, D(1)), r, ww), rhs)))))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula QualifiedHead(string owner, string name, params Formula[] args)
    {
        Formula[] parts = (owner + "." + name).Split('.').Select(part =>
            (Formula)Seq(Operatorname, Grp(Id(part)))).ToArray();
        Formula head = Seq(parts.SelectMany((part, index) =>
            index == 0 ? new[] { part } : new[] { Dot, part }).ToArray());
        return new Formula.Apply(head, [.. args]);
    }

    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Quantum/Entanglement/SequentialOccupationHistory." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/raveh2024dicke")),
            Blocks(Paragraph(Text(text))), role);

    private static Formula Id(string name) => F.Id(name);
    private static Formula a => Id("a");
    private static Formula b => Id("b");
    private static Formula n => Id("n");
    private static Formula t => Id("t");
    private static Formula s => Id("s");
    private static Formula c => Id("c");
    private static Formula beta => Id("beta");
    private static Formula initial => Id("initial");
    private static Formula w => Id("w");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Multi => Call("Multiset", Id("A"));
    private static Formula B(Formula time) => Call("B", a, time);
    private static Formula S => Call("S", a, t);
    private static Formula Output => Call("Prod", Id("A"), B(Add(t, D(1))));
    private static Formula Active => Lt(t, Card(a));
    private static Formula Word(Formula length) => Call("Word", Id("A"), length);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Dagger(Formula x) => Call("conjTranspose", x);
    private static Formula V(Formula length, Formula r, Formula word) => Call("V", length, r, word);
    private static Formula Cut(Formula chain, Formula time) => Call("cutBond", chain, time);
    private static Formula O(Formula length, Formula time) => Call("O", a, length, time);
    private static Formula P => Call("P", c, initial, t);
    private static Formula Q => Call("Q", c, t, s);
    private static Formula FixedLength => Eq(Call("length", c), Add(t, s));
    private static Formula ExactOutput => All("w", Word(Add(t, s)),
        Eq(Call("amp", c, initial, w), V(Add(t, s), a, w)));
    private static Formula ExactWholeOutput => All("w", Word(Card(a)),
        Eq(Call("amp", c, initial, w), V(Card(a), a, w)));
    private static Formula AchievableWitness => Exists("beta", Id("Type"),
        Exists("finite", Call("Fintype", beta), Exists("c", Call("FiniteChain", Id("A"), beta),
            Exists("initial", Call("Function", beta, C), And(Eq(Call("length", c), Card(a)),
                And(ExactWholeOutput, Eq(Call("maximumBond", c), Id("m"))))))));
    private static Formula Ast => Id("ast");
    private static Formula ConcreteChain => Call("O", Ast, Card(Ast), D(0));
    private static Formula SupAt(Formula limit, Formula body) =>
        Call("FinsetSup", Call("range", limit), Seq(t, Sp, Mapsto, Sp, body));
    private static Formula MaximumChainParameters(Formula body) => Alphabet(
        All("beta", Id("Type"), Imp(Call("Fintype", beta),
            All("c", Call("FiniteChain", Id("A"), beta),
                All("initial", Call("Function", beta, C), All("a", Multi, body))))));
    private static Formula ChainParameters(Formula body) => All("A", Id("Type"),
        All("beta", Id("Type"), Imp(Call("Fintype", beta),
            All("c", Call("FiniteChain", Id("A"), beta), body))));
    private static Formula ExactChainParameters(Formula body) => Alphabet(
        All("beta", Id("Type"), Imp(Call("Fintype", beta),
            All("c", Call("FiniteChain", Id("A"), beta),
                All("initial", Call("Function", beta, C), All("a", Multi,
                    All("t", N, All("s", N, body))))))));
    private static Formula SumAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Discrete(Formula body) => All("A", Id("Type"),
        Imp(Call("DecidableEq", Id("A")), body));
    private static Formula Alphabet(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A"))), body));
    private static Formula Parameters(Formula body) => Alphabet(All("a", Multi, All("t", N, body)));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
