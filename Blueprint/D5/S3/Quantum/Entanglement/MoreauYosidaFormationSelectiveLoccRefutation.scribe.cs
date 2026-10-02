using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class MoreauYosidaFormationSelectiveLoccRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/shirokov2026moreauyosidaeof");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shirokov's Moreau-Yosida approximation of the entanglement of formation can increase on average under a local projective measurement. The input value is at most 1/7 and the output average is at least 3/20, for lambda = 7/2 on C^5 tensor C^3.",
        H("Selective LOCC can increase the Moreau-Yosida entanglement of formation"),
        Blocks(
            Node("Coeff", "Pure-vector coefficients", CoeffFormula(),
                "Coeff(a,b) is the complex a by b coefficient matrix of a vector in C^a tensor C^b. Fin(a) labels Alice's basis and Fin(b) labels Bob's basis.", false),
            Node("mass", "Squared vector norm", MassFormula(),
                "The mass of M is the sum of the squared complex norms of all its entries. normSq(z) = |z|^2.", false),
            Node("Pure", "Normalized pure vectors", PureFormula(),
                "Pure(a,b) consists of coefficient matrices with mass one. Every normalized joint pure vector is represented, without a restriction to either selected block.", true),
            Node("Ensemble", "All finite pure ensembles", EnsembleFormula(),
                "Equation (EF-d), equation (1), p. 2: \"where the infimum is taken over all finite ensembles {pₖ, ϱₖ} of pure states in 𝔖(@HAB@) having @RHO@ as their average state\". rankOneDensity is the existing outer product of a vector with itself; the displayed lambda uncurries each coefficient matrix. An Ensemble(n,r) is a pair (p,q) of probabilities and normalized pure vectors satisfying every displayed condition. DensityState(Fin(a) times Fin(b)) is the canonical CStarMatrix density-state carrier, with nonnegative matrix and trace one. CStarMatrix.ofMatrix.symm returns the underlying joint matrix. No upper bound is imposed on n; the convex roof below ranges over all n.", true),
            Node("cost", "Average pure-state entropy", CostFormula(),
                "The average entropy is the probability-weighted vonNeumannEntropy of marginalRight of each pureDensityState. The unit-norm proof argument to pureDensityState is suppressed in the display and supplied by mass(val(ψ(e)(i))) = 1. pureDensityState is the existing density-state constructor with underlying matrix rankOneDensity, the outer product |ψ><ψ|. marginalRight traces out Bob and retains Alice. vonNeumannEntropy is the existing -Re Tr(rho log rho), using natural logarithms and zero contribution at a zero eigenvalue. The projections p(e) and ψ(e) are its probabilities and pure vectors, respectively.", true),
            Node("E_F", "Entanglement of formation", FormationFormula(),
                "Equation (EF-d), equation (1), p. 2, is E_F(rho) = inf_{sum_k p_k varrho_k = rho} sum_k p_k S([varrho_k]_A). The formula uses all finite ensembles as in the quoted sentence above. The displayed full name E with subscript F denotes the Lean definition E_F. The value type is the extended nonnegative reals; ofReal(x) is max(x,0) in that type. For normalized pure states every entropy term is nonnegative.", true),
            Node("E_F_my", "The unsquared trace-norm Moreau envelope", EnvelopeFormula(),
                "Equation (EFA), equation (13), p. 6, defines E_F^lambda(rho) = inf_sigma { E_F(sigma) + @DIST@/(2 lambda) }. The footnote on p. 7 states: \"It is essential that we use @DIST@ instead of @DISTSQ@ in (13).\" The displayed full name E with nested subscript F and my denotes the Lean definition E_F_my; t denotes lambda. The infimum ranges over every density state on the same space. traceNorm is the existing matrix trace norm, and the penalty has no square. The selective claim requires t > 0.", true),
            Node("LocalInstrument", "Local instruments with classical outcomes", InstrumentFormula(),
                "A local instrument on dimension d has o classical outcomes, k(i) Kraus operators for outcome i, and operators K(i,j) with the displayed completeness equation. conjTranspose is Matrix.conjTranspose. All sums are finite. Multiple Kraus operators for one classical outcome represent a general completely positive outcome map on the fixed local space.", true),
            Node("Protocol", "Finite-round LOCC with recorded outcomes", ProtocolFormula(),
                "Protocol(a,b) is the inductive type with constructors done, alice and bob. The two local constructors take an instrument and a continuation for each classical outcome. Finite trees retain the complete classical outcome history. This class has finite outcomes and rounds and fixed local spaces. It contains one-round local projective measurements, hence the counterexample also refutes selective monotonicity for every larger LOCC class containing these operations.", true),
            Node("branchList", "Unnormalized terminal branches", BranchFormula(),
                "The recursive equations evaluate the complete protocol on a joint matrix r. At an Alice node each local Kraus operator is tensored with Bob's identity, and at a Bob node Alice's identity is tensored with the local Kraus operator. flatMap concatenates the terminal branch lists over the classical outcomes. The typed matrix numerals 1 are the identity matrices; conjTranspose is Matrix.conjTranspose. These are unnormalized branches. A terminal probability and normalized output are linked by the exact matrix equation in claim.", true),
            Node("claim", "Shirokov's selective-monotonicity conjecture", ClaimFormula(),
                "Section 7, p. 20: \"So, we may conjecture, at the moment, that the function @EF@ does not increase under selective LOCC-operations as well.\" The section's heading is \"Open question: can the function @EF@ increase under selective LOCC-operations?\" The formal inequality is the standard selective convention: the probability-weighted average of the normalized terminal values is at most the input value. Dimensions a,b are positive, t is lambda > 0, T is a finite-round local-instrument protocol, p is nonnegative and sums to one, and out assigns normalized density states. finRange(n) is the ordered list of all elements of Fin(n); its map lists p(i) times CStarMatrix.ofMatrix.symm(val(out(i))) in the same order as the terminal branches. Complex(p(i)) denotes the real-to-complex coercion, and ofReal(p(i)) denotes the extended-nonnegative weight. Zero-probability branches may have any normalized out(i).", true),
            Result()),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("shirokov-" + declaration.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(SourceProse(prose)), DescribeRole.Definition);

    private static DocumentBlock SourceProse(string prose)
    {
        var parts = prose.Split('@');
        var content = new System.Collections.Generic.List<Inline>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i % 2 == 0)
            {
                if (parts[i].Length > 0) content.Add(Text(parts[i]));
                continue;
            }
            Formula norm = Seq(Vert,Sp,Subtract(Rho,SigmaLower),Sp,Vert);
            Formula sourceMath = parts[i] switch
            {
                "EF" => Seq(F.Id("E"),Caret,Grp(LambdaLower),Underscore,Grp(F.Id("F"))),
                "HAB" => new Formula.Subscript(Seq(Mathcal,Grp(F.Id("H"))),F.Id("AB")),
                "RHO" => Rho,
                "DIST" => new Formula.Subscript(norm,D(1)),
                "DISTSQ" => Seq(norm,Caret,Grp(D(2)),Underscore,Grp(D(1))),
                _ => throw new System.InvalidOperationException("Unknown source quotation symbol.")
            };
            content.Add(Math(sourceMath));
        }
        return Paragraph([..content]);
    }

    private static DocumentBlock Result() => Describe.Lean(
        DescribeId.Create("shirokov-result"), DeclarationHandle.Create(Prefix + "result"),
        H("A local projective measurement increases the output average"),
        StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
        AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(
            "Let v_2 = e_00 + e_11 and v_3 = e_20 + e_31 + e_42 on C^5 tensor C^3, let Phi_2 = v_2 v_2^*/2 and Phi_3 = v_3 v_3^*/3, and omega = (Phi_2 + Phi_3)/2. At t = 7/2 Alice measures the projections diag(1,1,0,0,0) and its complement. The two branches have probabilities 1/2 and outputs Phi_2 and Phi_3. For every normalized ambient 5 by 3 pure coefficient matrix, entropy is at least 1 - Tr((M M^*)^2), equal to twice the sum of the squared absolute 2 by 2 minors. Pair and triple norm estimates give affine entropy bounds with slope 3/10 and fidelity offsets 11/20 and 2/5. Nonnegativity lowers the slope to 2/7; linearity extends the bounds to every finite ensemble. The unitary reflection 2P-I gives traceNorm(P-sigma) >= 2(1-Tr(P sigma)) for a trace-one projector P. Thus E_F_my(7/2,Phi_2) >= 9/70 and E_F_my(7/2,Phi_3) >= 6/35, and their average is at least 3/20. The state sigma = (|00><00| + |11><11|)/2 has an explicit product-state ensemble of entropy zero, and traceNorm(omega-sigma) <= 1, so E_F_my(7/2,omega) <= 1/7. Since 3/20 - 1/7 = 1/140 > 0, the selective inequality fails."))),
        DescribeRole.Theorem);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeqTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, y);
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Arr(Formula x, Formula y) => Parenthesized(Seq(x, Sp, To, Sp, y));
    private static Formula ProdType(Formula x, Formula y) => Parenthesized(Seq(x, Sp, F.Times, Sp, y));
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Typed(string name, Formula type) => Seq(F.Id(name), Sp, Colon, Sp, type);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(name,type), Comma, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(name,type)), Sp, body);
    private static Formula InfOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Seq(Operatorname,Grp(F.Id("inf"))), Typed(name,type)), Sp, Parenthesized(body));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Val(Formula x) => Call("val",x);
    private static Formula EfName() => new Formula.Subscript(F.Id("E"), F.Id("F"));
    private static Formula MyName() => new Formula.Subscript(F.Id("E"), new Formula.Subscript(F.Id("F"), F.Id("my")));
    private static Formula Adj(Formula x) => Call("conjTranspose",x);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula N => F.Id("n");
    private static Formula M => F.Id("M");
    private static Formula R => F.Id("r");
    private static Formula S => F.Id("s");
    private static Formula I => F.Id("I");
    private static Formula K => F.Id("k");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula CoeffType() => Call("Coeff",A,B);
    private static Formula JointType() => Call("CompositeMatrix",A,B);
    private static Formula StateType() => Call("DensityState",ProdType(Fin(A),Fin(B)));
    private static Formula StateMatrix(Formula x) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm"))),
            [Val(x)]);
    private static Formula PureType() => Call("Pure",A,B);
    private static Formula ProtocolType() => Call("Protocol",A,B);
    private static Formula Dims(Formula body) => All("a",Nat(),All("b",Nat(),body));
    private static Formula MatrixType(Formula rows, Formula cols) => Call("Matrix",rows,cols,Complex());
    private static Formula Subset(string variable, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(variable,type), Sp, Mid, Sp, condition, CloseBrace);

    private static Formula CoeffFormula() => Dims(Eqn(CoeffType(), MatrixType(Fin(A),Fin(B))));
    private static Formula MassFormula() => Dims(All("M",CoeffType(),Eqn(Call("mass",M),
        SumOver("i",Fin(A),SumOver("j",Fin(B),Call("normSq",At(M,F.Id("i"),F.Id("j"))))))));
    private static Formula PureFormula() => Dims(Eqn(PureType(),Subset("M",CoeffType(),Eqn(Call("mass",M),D(1)))));

    private static Formula EnsembleFormula()
    {
        Formula pairType = ProdType(Arr(Fin(N),Real()),Arr(Fin(N),PureType()));
        Formula conditions = And(All("i",Fin(N),LeqTo(D(0),At(P,F.Id("i")))),
            And(Eqn(SumOver("i",Fin(N),At(P,F.Id("i"))),D(1)),
                Eqn(SumOver("i",Fin(N),Mul(Call("Complex",At(P,F.Id("i"))),
                    Call("rankOneDensity",Lam("x",ProdType(Fin(A),Fin(B)),At(Val(At(Q,F.Id("i"))),Call("fst",F.Id("x")),Call("snd",F.Id("x"))))))),StateMatrix(R))));
        Formula set = Seq(OpenBrace, Pair(P,Q), Sp, Colon, Sp, pairType, Sp, Mid, Sp, conditions, CloseBrace);
        return Dims(All("n",Nat(),All("r",StateType(),Eqn(Call("Ensemble",N,R),set))));
    }
    private static Formula CostFormula()
    {
        Formula e = F.Id("e"), i = F.Id("i"), x = F.Id("x");
        Formula coefficients = Val(At(At(new Formula.Psi(),e),i));
        Formula vector = Lam("x",ProdType(Fin(A),Fin(B)),
            At(coefficients,Call("fst",x),Call("snd",x)));
        Formula entropy = Call("vonNeumannEntropy",Call("marginalRight",Call("pureDensityState",vector)));
        return Dims(All("n",Nat(),All("r",StateType(),All("e",Call("Ensemble",N,R),
            Eqn(Call("cost",e),SumOver("i",Fin(N),Mul(At(Call("p",e),i),entropy)))))));
    }
    private static Formula FormationFormula() => Dims(All("r",StateType(),Eqn(At(EfName(),R),
        InfOver("n",Nat(),InfOver("e",Call("Ensemble",N,R),Call("ofReal",Call("cost",F.Id("e"))))))));
    private static Formula EnvelopeFormula() => Dims(All("t",Real(),All("r",StateType(),
        Eqn(At(MyName(),F.Id("t"),R),InfOver("s",StateType(),
            Add(At(EfName(),S),Call("ofReal",new Formula.Fraction(
                Call("traceNorm",Subtract(StateMatrix(R),StateMatrix(S))),Mul(D(2),F.Id("t"))))))))));

    private static Formula InstrumentFormula()
    {
        Formula o = F.Id("o"), ops = F.Id("K"), d = F.Id("d");
        Formula mat = MatrixType(Fin(d),Fin(d));
        Formula tuple = Parenthesized(Seq(o,Comma,Sp,K,Comma,Sp,ops));
        Formula sigmaType = Seq(Sigma, Sp, Parenthesized(Typed("o",Nat())), Comma, Sp,
            Sigma, Sp, Parenthesized(Typed("k",Arr(Fin(o),Nat()))), Comma, Sp,
            All("i",Fin(o),Arr(Fin(At(K,F.Id("i"))),mat)));
        Formula complete = Eqn(SumOver("i",Fin(o),SumOver("j",Fin(At(K,F.Id("i"))),
            Mul(Adj(At(ops,F.Id("i"),F.Id("j"))),At(ops,F.Id("i"),F.Id("j"))))),D(1));
        return All("d",Nat(),Eqn(Call("LocalInstrument",d),
            Seq(OpenBrace,tuple,Sp,Colon,Sp,sigmaType,Sp,Mid,Sp,complete,CloseBrace)));
    }
    private static Formula ProtocolFormula()
    {
        Formula local(string dim) => All("I",Call("LocalInstrument",F.Id(dim)),
            Arr(Arr(Fin(Call("outcomes",I)),ProtocolType()),ProtocolType()));
        return Dims(Seq(Seq(ProtocolType(), Sp, Colon, Sp, F.Id("Type")), Semi, Sp,
            Typed("done",ProtocolType()), Semi, Sp,
            Typed("alice",local("a")), Semi, Sp, Typed("bob",local("b"))));
    }
    private static Formula BranchFormula()
    {
        Formula continuationType = Arr(Fin(Call("outcomes",I)),ProtocolType());
        Formula branch(bool alice)
        {
            Formula op = alice ? Call("kronecker",At(Call("K",I),F.Id("i"),F.Id("j")),Parenthesized(Seq(D(1), Sp, Colon, Sp, MatrixType(Fin(B),Fin(B)))))
                : Call("kronecker",Parenthesized(Seq(D(1), Sp, Colon, Sp, MatrixType(Fin(A),Fin(A)))),At(Call("K",I),F.Id("i"),F.Id("j")));
            Formula nextMatrix = SumOver("j",Fin(At(Call("krausCount",I),F.Id("i"))),Mul(Mul(op,R),Adj(op)));
            Formula body = Eqn(Call("branchList",Call(alice ? "alice" : "bob",I,K),R),
                Call("flatMap",Lam("i",Fin(Call("outcomes",I)),Call("branchList",At(K,F.Id("i")),nextMatrix)),
                    Call("finRange",Call("outcomes",I))));
            return All("I",Call("LocalInstrument",alice ? A : B),All("k",continuationType,body));
        }
        Formula done = Eqn(Call("branchList",Call("done",A,B),R),Seq(OpenBracket,R,CloseBracket));
        return Dims(All("r",JointType(),And(done,And(branch(true),branch(false)))));
    }
    private static Formula ClaimFormula()
    {
        Formula output = F.Id("out"), t = F.Id("t"), i = F.Id("i"), T = F.Id("T");
        Formula branches = Eqn(Call("branchList",T,StateMatrix(R)),Call("map",Lam("i",Fin(N),
            Mul(Call("Complex",At(P,i)),StateMatrix(At(output,i)))),Call("finRange",N)));
        Formula inequality = LeqTo(SumOver("i",Fin(N),Mul(Call("ofReal",At(P,i)),
            At(MyName(),t,At(output,i)))),At(MyName(),t,R));
        Formula body = Imp(All("i",Fin(N),LeqTo(D(0),At(P,i))),
            Imp(Eqn(SumOver("i",Fin(N),At(P,i)),D(1)),Imp(branches,inequality)));
        body = All("out",Arr(Fin(N),StateType()),body);
        body = All("p",Arr(Fin(N),Real()),body);
        body = All("n",Nat(),body);
        body = All("T",ProtocolType(),body);
        body = All("r",StateType(),body);
        body = All("t",Real(),Imp(LtTo(D(0),t),body));
        body = All("a",Nat(),All("b",Nat(),Imp(LtTo(D(0),A),Imp(LtTo(D(0),B),body))));
        return IffTo(F.Id("claim"),body);
    }
}
