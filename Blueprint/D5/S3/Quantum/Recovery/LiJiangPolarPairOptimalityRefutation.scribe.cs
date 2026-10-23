using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class LiJiangPolarPairOptimalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/lijiang2026highrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A feasible qubit rank-one encoder strictly improves the source polar pair.",
        H("Li–Jiang polar-pair optimality: an exact finite-noise refutation"),
        Blocks(
            Def("lambda1", "First source parameter", Parameters("lambda1"), "Source Eq. 18: d is the logical dimension and p is the noise parameter."),
            Def("lambda4", "Fourth source parameter", Parameters("lambda4"), "Source Eq. 18; the denominator is d squared."),
            Def("lambda5", "Fifth source parameter", Parameters("lambda5"), "Source Eq. 18; the claim restricts p to the open interval (0,1)."),
            Def("lambda2", "Second source parameter", Parameters("lambda2"), "Source Eq. 18, with lambda1 and lambda4 as defined above."),
            Def("lambda3", "Third source parameter", Parameters("lambda3"), "Source Eq. 18, with the factor 2 in the numerator."),
            Def("sourceQ", "Source positive matrix", QFormula(), "Literal Eq. 18, with identity on the code space and maxEntangled(Fin(d)) on the same space. Square roots are the real nonnegative square roots, embedded into the complex matrices."),
            Def("sourceD", "Right-factor trace Kraus matrices", DFormula(), "Eq. 19: D_j = I_L tensor bra(j). Its row a and column (b,k) entry is 1 exactly when a=b and j=k. Thus it removes the right factor."),
            Def("sourceB", "Source products", BFormula(), "Eqs. 19–21: B_ij = Q D_i adjoint D_j. The order of the two indices is retained."),
            Def("sourceE", "Source orthonormal matrices", EFormula(), "Literal Eq. 22, including B_ij adjoint. The ket e_ij is the product-basis vector and psi is maxEntangledVector(Fin(d))."),
            Def("sourceNoise", "Source noise on all matrices", NoiseFormula(), "Literal all-matrix Eq. 23. The identity in the first term acts on the code space; the identity in the Kronecker term acts on the auxiliary factor. Neither input nor output is normalized by its trace."),
            Def("sourceC", "Source polar column matrix", CFormula(), "Supplement Eq. S60: chi is an auxiliary vector, and sourceC is Q times the column map I tensor ket(chi)."),
            Def("sourcePolar", "Source polar encoder", PolarFormula(), "Eq. S60. CFC.sqrt is the ordered positive square root, and CStarMatrix.ofMatrix.symm transports it back to a matrix. The square root is the ordered positive CFC square root of the actual Gram matrix, transported through that equivalence; the inverse is the matrix inverse."),
            RepoDef("matrixAction", "Matrix action of a completely positive map", ActionFormula(), "The carrier is CompletelyPositiveMap on the finite CStarMatrix algebras, so complete positivity means positivity at every amplification. ofMatrix is CStarMatrix.ofMatrix, and CStarMatrix.ofMatrix.symm is its inverse; they transport input and output matrices across that equivalence."),
            Def("TraceNonincreasing", "Trace constraint on every positive input", TNIFormula(), "Eq. 13 permits trace-nonincreasing encoding and decoding. X ranges over every positive semidefinite matrix, and Re extracts the real part of its trace."),
            Def("inputFirstChoi", "Input-first Choi convention", ChoiFormula(), "MatrixMap denotes PhyslibLeaf.MatrixMap, whose PhyslibLeaf.MatrixMap.choi_matrix gives the output-first Choi matrix. The source's input-first convention is obtained by swapping both product indices of that output-first Choi matrix. The reindexing uses Equiv.prodComm(b,a)."),
            Def("entanglementFidelity", "Unrenormalized canonical-purification fidelity", FidelityFormula(), "The shared maxEntangledVector(Fin(d)) is the normalized purification of I/d, in logical-factor-first product order, and maxEntangled(Fin(d)) is its rank-one projector. This is the source overlap for tau=I/d: apply the logical channel to the first purification factor and the identity to the reference factor, then take the real overlap. No output trace division is made, including for trace-decreasing competitors."),
            Def("claim", "Full fixed-noise polar-pair dominance assertion", ClaimFormula(), "Li and Jiang, arXiv:2609.00778v1, printed p. 17 after Eq. S64: 'Exact optimality of this pair at fixed p > 0 remains open.' The antecedent is the Eq. S60 polar encoder and the actual right partial trace. The claim quantifies over every natural d >= 2, every real 0 < p < 1, every unit complex auxiliary vector chi, and every completely positive trace-nonincreasing encoder C and decoder D with input-first encoder Choi rank at most one. PhyslibLeaf.MatrixMap.of_kraus constructs the single-Kraus map, and comp composes maps in outer-then-inner order. Competitors are arbitrary members of that class, rather than just the isometric pairs used in the refutation."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A feasible qubit pair strictly improves the source polar pair"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(F.Id("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At d=2, p=9/13 and chi=ket(0), the source polar columns are (3ket(00)-ket(11))/sqrt(10) and ket(10). The competitor columns are (24ket(00)-7ket(11))/25 and ket(10), with the same actual right partial trace decoder. The proof identifies the positive Gram square root and its inverse, gives the actual source noise 24 complete Kraus matrices, and uses the 48 decoder-noise-encoder composite matrices. It bridges canonical-purification fidelity to the Kraus trace sum and proves both pairs feasible in the full all-amplification CP/TNI class, with input-first encoder Choi rank at most one. The source polar fidelity is 1537/4160 + 7sqrt(10)/80; the competitor fidelity is 336031/520000. Their difference is 7(10279-3250sqrt(10))/260000 > 0, using 10279 squared minus 10 times 3250 squared = 32841. This refutes exact finite-noise dominance. It determines no global rank-one optimum and does not refute the source's optimal quadratic asymptotic coefficient."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("li-jiang-2026-fixed-noise-polar-pair-optimality-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, AssessedProvenance.FromLiterature(Source));
    private static DocumentBlock RepoDef(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, AssessedProvenance.FromRepo(Source));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (string part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(part switch
            {
                "D5" => Seq(F.Id("D"), D(5)),
                "S3" => Seq(F.Id("S"), D(3)),
                "choi_matrix" => Seq(F.Id("choi"), Esc, Underscore, Grp(F.Id("matrix"))),
                "of_kraus" => Seq(F.Id("of"), Esc, Underscore, Grp(F.Id("kraus"))),
                _ => F.Id(part)
            });
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Inst(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula WithFiniteIndices(Formula body) =>
        All("a", Seq(F.Id("Type"), Star), Inst(Fn("Fintype", F.Id("a")),
            Inst(Fn("DecidableEq", F.Id("a")), All("b", Seq(F.Id("Type"), Star),
                Inst(Fn("Fintype", F.Id("b")), Inst(Fn("DecidableEq", F.Id("b")), body))))));
    private static Formula N(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Fn(string name, params Formula[] args) => new Formula.Apply(N(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Named(string name, Formula value) => Parenthesized(Seq(F.Id(name), Sp, Colon, Eq, Sp, value));
    private static Formula Smul(Formula scalar, Formula value) => At(Qualified("HSMul", "hSMul"), scalar, value);
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula ToReal(Formula value) => new Formula.Subscript(Fn("val", value), RealType);
    private static Formula AndTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula PlusTo(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula f) => new Formula.Power(Parenthesized(f), D(2));
    private static Formula Inv(Formula f) => new Formula.Power(Parenthesized(f), new Formula.Negate(D(1)));
    private static Formula Adj(Formula f) => Fn("conjTranspose", f);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula Cases(Formula condition, Formula yes, Formula no) => Seq(N("if"), Sp, Parenthesized(condition), Sp, N("then"), Sp, Parenthesized(yes), Sp, N("else"), Sp, Parenthesized(no));
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula d) => Fn("Fin", d);
    private static Formula Prod(Formula a, Formula b) => Parenthesized(Seq(a, Times, b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula Lam(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id(name), Colon, type, Mapsto, body));
    private static Formula Code(Formula d) => Prod(FinOf(d), FinOf(d));
    private static Formula Mat(Formula a, Formula b) => Fn("Matrix", a, b, ComplexType);
    private static Formula CP(Formula a, Formula b) => Fn("CompletelyPositiveMap", Fn("CStarMatrix", a, a, ComplexType), Fn("CStarMatrix", b, b, ComplexType));
    private static Formula Map(Formula a, Formula b) => Fn("MatrixMap", a, b, ComplexType);
    private static Formula WithDP(Formula body) => Disp(All("d", NatType, All("p", RealType, body)));

    private static Formula Parameters(string name)
    {
        Formula d=F.Id("d"), p=F.Id("p"), d2=Sq(ToReal(d)), l1=Fn("lambda1",d,p), l4=Fn("lambda4",d,p);
        Formula rhs = name switch
        {
            "lambda1" => Sub(D(1),Fr(p,Sub(d2,D(2)))),
            "lambda4" => Fr(PlusTo(Sub(d2,D(1)),p),d2),
            "lambda5" => Fr(Sub(D(1),p),d2),
            "lambda2" => Fr(Mul(Sub(D(1),l1),Sub(Mul(d2,l1),D(1))),Mul(d2,l4)),
            "lambda3" => Fr(Mul(D(2),Sq(Sub(D(1),l1))),Mul(d2,l4)),
            _ => throw new System.ArgumentException(nameof(name))
        };
        return WithDP(EqTo(Fn(name,d,p),rhs));
    }
    private static Formula QFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),pi=Fn("maxEntangled",FinOf(d));
        return WithDP(EqTo(Fn("sourceQ",d,p),Smul(OfReal(Fn("sqrt",ToReal(d))),PlusTo(Smul(OfReal(Fn("sqrt",Fr(Fn("lambda4",d,p),Sub(Sq(ToReal(d)),D(1))))),Sub(D(1),pi)),Smul(OfReal(Fn("sqrt",Fn("lambda5",d,p))),pi)))));
    }
    private static Formula DFormula()
    {
        Formula d=F.Id("d"),j=F.Id("j"),a=F.Id("a"),b=F.Id("b"),k=F.Id("k");
        return Disp(All("d",NatType,All("j",FinOf(d),All("a",FinOf(d),All("b",FinOf(d),All("k",FinOf(d),EqTo(At(Fn("sourceD",d,j),a,Pair(b,k)),Cases(AndTo(EqTo(a,b),EqTo(j,k)),D(1),D(0)))))))));
    }
    private static Formula BFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),i=F.Id("i"),j=F.Id("j");
        return WithDP(All("i",FinOf(d),All("j",FinOf(d),EqTo(Fn("sourceB",d,p,Pair(i,j)),Mul(Mul(Fn("sourceQ",d,p),Adj(Fn("sourceD",d,i))),Fn("sourceD",d,j))))));
    }
    private static Formula EFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),ij=F.Id("ij"),a=F.Id("a");
        Formula basis=Lam("a",Code(d),Cases(EqTo(a,ij),D(1),D(0)));
        return WithDP(All("ij",Code(d),EqTo(Fn("sourceE",d,p,ij),Smul(OfReal(Inv(Fn("sqrt",Fn("lambda4",d,p)))),Sub(Fn("vecMulVec",basis,Fn("star",Fn("maxEntangledVector",FinOf(d)))),Smul(OfReal(Fn("sqrt",Fn("lambda5",d,p))),Adj(Fn("sourceB",d,p,ij))))))));
    }
    private static Formula NoiseFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),x=F.Id("X"),ij=F.Id("ij"),q=Fn("sourceQ",d,p),e=Fn("sourceE",d,p,ij);
        Formula first=Smul(OfReal(Fn("lambda3",d,p)),Smul(Fn("trace",x),D(1)));
        Formula second=Smul(OfReal(Sub(Fn("lambda1",d,p),Fn("lambda3",d,p))),Fn("kronecker",Fn("partialTraceRight",Mul(Mul(q,x),q)),D(1)));
        Formula third=Smul(OfReal(Fn("lambda2",d,p)),SumOver("ij",Code(d),Mul(Mul(e,x),Adj(e))));
        return WithDP(All("X",Mat(Code(d),Code(d)),EqTo(Fn("sourceNoise",d,p,x),PlusTo(PlusTo(first,second),third))));
    }
    private static Formula CFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),chi=F.Id("chi"),a=F.Id("a"),b=F.Id("b");
        Formula columns=Fn("of",Lam("a",Code(d),Lam("b",FinOf(d),Cases(EqTo(Fn("fst",a),b),At(chi,Fn("snd",a)),D(0)))));
        return WithDP(All("chi",new Formula.TypeArrow(FinOf(d),ComplexType),EqTo(Fn("sourceC",d,p,chi),Mul(Fn("sourceQ",d,p),columns))));
    }
    private static Formula PolarFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),chi=F.Id("chi"),c=Fn("sourceC",d,p,chi);
        Formula root=At(Qualified("CStarMatrix", "ofMatrix", "symm"),At(Qualified("CFC", "sqrt"),Fn("ofMatrix",Mul(Adj(c),c))));
        return WithDP(All("chi",new Formula.TypeArrow(FinOf(d),ComplexType),EqTo(Fn("sourcePolar",d,p,chi),Mul(c,Inv(root)))));
    }
    private static Formula ActionFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),x=F.Id("X");
        return Disp(WithFiniteIndices(All("f",CP(a,b),All("X",Mat(a,a),EqTo(Fn("matrixAction",f,x),At(Qualified("CStarMatrix", "ofMatrix", "symm"),At(f,Fn("ofMatrix",x))))))));
    }
    private static Formula TNIFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),x=F.Id("X");
        Formula body=All("X",Mat(a,a),Imp(Fn("PosSemidef",x),LeTo(Fn("Re",Fn("trace",Fn("matrixAction",f,x))),Fn("Re",Fn("trace",x)))));
        return Disp(WithFiniteIndices(All("f",CP(a,b),IffTo(Fn("TraceNonincreasing",f),body))));
    }
    private static Formula ChoiFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),swap=Fn("prodComm",b,a);
        return Disp(WithFiniteIndices(All("f",Map(a,b),EqTo(Fn("inputFirstChoi",f),Fn("reindex",swap,swap,At(Qualified("PhyslibLeaf", "MatrixMap", "choi_matrix"),f))))));
    }
    private static Formula FidelityFormula()
    {
        Formula d=F.Id("d"),f=F.Id("f"),psi=Fn("maxEntangledVector",FinOf(d));
        Formula output=Fn("kron",f,N("id"),Fn("maxEntangled",FinOf(d)));
        return Disp(All("d",NatType,All("f",Map(FinOf(d),FinOf(d)),EqTo(Fn("entanglementFidelity",d,f),Fn("Re",Fn("dotProduct",Fn("star",psi),Fn("mulVec",output,psi)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),chi=F.Id("chi"),c=F.Id("C"),dec=F.Id("D"),i=F.Id("i");
        Formula actionC=Fn("matrixAction",c),actionD=Fn("matrixAction",dec),noise=Fn("sourceNoise",d,p),polar=Fn("sourcePolar",d,p,chi);
        Formula single=Parenthesized(Seq(Underscore, Colon, N("Unit"), Mapsto, polar));
        Formula rhs=Fn("entanglementFidelity",d,Fn("comp",At(Qualified("D5", "S3", "QuantumChannels", "PassiveMemoryNonclassicalRefutation", "discardMemory"), Named("d", d), Named("r", d)),Fn("comp",noise,At(Qualified("PhyslibLeaf", "MatrixMap", "of_kraus"),single,single))));
        Formula lhs=Fn("entanglementFidelity",d,Fn("comp",actionD,Fn("comp",noise,actionC)));
        Formula competitors=All("C",CP(FinOf(d),Code(d)),All("D",CP(Code(d),FinOf(d)),Imp(Fn("TraceNonincreasing",c),Imp(Fn("TraceNonincreasing",dec),Imp(LeTo(Fn("rank",Fn("inputFirstChoi",actionC)),D(1)),LeTo(lhs,rhs))))));
        Formula body=All("d",NatType,Imp(LeTo(D(2),d),All("p",RealType,Imp(LtTo(D(0),p),Imp(LtTo(p,D(1)),All("chi",new Formula.TypeArrow(FinOf(d),ComplexType),Imp(EqTo(SumOver("i",FinOf(d),Fn("normSq",At(chi,i))),D(1)),competitors)))))));
        return Disp(IffTo(F.Id("claim"),body));
    }
}
