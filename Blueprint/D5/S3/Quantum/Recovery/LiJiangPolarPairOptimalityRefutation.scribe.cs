using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class LiJiangPolarPairOptimalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quantum/lijiang2026highrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(GidRef.Create(Prefix[..^1]), StrataLint.Engine.Generality.General,
            GidRef.Create("D5/B/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation"),
            new EvidenceMirror.Waiver(WaiverReason.Create("finite-algebraic-proof")), [],
            Digest.Create("A feasible qubit rank-one encoder strictly improves the source polar pair.")),
        H("Li–Jiang polar-pair optimality: an exact finite-noise refutation"),
        Blocks(
            Def("lambda1", "First source parameter", Parameters("lambda1"), "Source Eq. 18: d is the logical dimension and p is the noise parameter."),
            Def("lambda4", "Fourth source parameter", Parameters("lambda4"), "Source Eq. 18; the denominator is d squared."),
            Def("lambda5", "Fifth source parameter", Parameters("lambda5"), "Source Eq. 18; the claim restricts p to the open interval (0,1)."),
            Def("lambda2", "Second source parameter", Parameters("lambda2"), "Source Eq. 18, with lambda1 and lambda4 as defined above."),
            Def("lambda3", "Third source parameter", Parameters("lambda3"), "Source Eq. 18, with the factor 2 in the numerator."),
            Def("canonicalPurification", "Canonical purification of the maximally mixed state", PurificationFormula(), "For positive d this is the normalized purification of I/d. Physical product order is logical factor first, auxiliary factor second; star conjugates vector entries. Product indices (a,b) are ordered pairs, not tensor products of scalar indices."),
            Def("sourcePi", "Canonical purification projector", PiFormula(), "The outer product vecMulVec(psi,star(psi)) is the source projector in Eq. 18."),
            Def("sourceQ", "Source positive matrix", QFormula(), "Literal Eq. 18, with identity on the code space and sourcePi on the same space. Square roots are the real nonnegative square roots, embedded into the complex matrices."),
            Def("sourceD", "Right-factor trace Kraus matrices", DFormula(), "Eq. 19: D_j = I_L tensor bra(j). Its row a and column (b,k) entry is 1 exactly when a=b and j=k. Thus it removes the right factor."),
            Def("sourceB", "Source products", BFormula(), "Eqs. 19–21: B_ij = Q D_i adjoint D_j. The order of the two indices is retained."),
            Def("sourceE", "Source orthonormal matrices", EFormula(), "Literal Eq. 22, including B_ij adjoint. The ket e_ij is the product-basis vector and psi is canonicalPurification(d)."),
            Def("rightTrace", "Actual right partial trace", RightFormula(), "The map is partialTraceRight from the existing library. It acts on every complex input matrix and retains the left factor."),
            Def("sourceNoise", "Source noise on all matrices", NoiseFormula(), "Literal all-matrix Eq. 23. The identity in the first term acts on the code space; the identity in the Kronecker term acts on the auxiliary factor. Neither input nor output is normalized by its trace."),
            Def("sourceC", "Source polar column matrix", CFormula(), "Supplement Eq. S60: chi is an auxiliary vector, and sourceC is Q times the column map I tensor ket(chi)."),
            Def("sourcePolar", "Source polar encoder", PolarFormula(), "Eq. S60. CFCsqrt denotes CFC.sqrt and ofMatrixInverse denotes CStarMatrix.ofMatrix.symm. The square root is the ordered positive CFC square root of the actual Gram matrix, transported through that equivalence; the inverse is the matrix inverse."),
            RepoDef("matrixAction", "Matrix action of a completely positive map", ActionFormula(), "The carrier is CompletelyPositiveMap on the finite CStarMatrix algebras, so complete positivity means positivity at every amplification. FiniteIndex abbreviates an arbitrary finite index type with Fintype and DecidableEq instances. ofMatrix is CStarMatrix.ofMatrix, and ofMatrixInverse is its inverse CStarMatrix.ofMatrix.symm; they transport input and output matrices across that equivalence."),
            Def("TraceNonincreasing", "Trace constraint on every positive input", TNIFormula(), "Eq. 13 permits trace-nonincreasing encoding and decoding. X ranges over every positive semidefinite matrix, and Re extracts the real part of its trace."),
            Def("inputFirstChoi", "Input-first Choi convention", ChoiFormula(), "MatrixMap denotes PhyslibLeaf.MatrixMap, and choiMatrix denotes its choi_matrix. The source's input-first convention is obtained by swapping both product indices of that output-first Choi matrix. The reindexing uses Equiv.prodComm(b,a)."),
            Def("entanglementFidelity", "Unrenormalized canonical-purification fidelity", FidelityFormula(), "This is the source overlap for tau=I/d: apply the logical channel to the first purification factor and the identity to the reference factor, then take the real overlap. No output trace division is made, including for trace-decreasing competitors."),
            Def("claim", "Full fixed-noise polar-pair dominance assertion", ClaimFormula(), "Li and Jiang, arXiv:2609.00778v1, printed p. 17 after Eq. S64: 'Exact optimality of this pair at fixed p > 0 remains open.' The antecedent is the Eq. S60 polar encoder and the actual right partial trace. The claim quantifies over every natural d >= 2, every real 0 < p < 1, every unit complex auxiliary vector chi, and every completely positive trace-nonincreasing encoder C and decoder D with input-first encoder Choi rank at most one. ofKraus denotes PhyslibLeaf.MatrixMap.of_kraus, and comp composes maps in outer-then-inner order. Competitors are arbitrary members of that class, rather than just the isometric witnesses used to refute it."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A feasible qubit pair strictly improves the source polar pair"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At d=2, p=9/13 and chi=ket(0), the source polar columns are (3ket(00)-ket(11))/sqrt(10) and ket(10). The competitor columns are (24ket(00)-7ket(11))/25 and ket(10), with the same actual right partial trace decoder. The proof identifies the positive Gram square root and its inverse, gives the actual source noise 24 complete Kraus matrices, and uses the 48 decoder-noise-encoder composite matrices. It bridges canonical-purification fidelity to the Kraus trace sum and proves both witnesses feasible in the full all-amplification CP/TNI class, with input-first encoder Choi rank at most one. The source polar fidelity is 1537/4160 + 7sqrt(10)/80; the competitor fidelity is 336031/520000. Their difference is 7(10279-3250sqrt(10))/260000 > 0, using 10279 squared minus 10 times 3250 squared = 32841. This refutes exact finite-noise dominance. It determines no global rank-one optimum and does not refute the source's optimal quadratic asymptotic coefficient."))),
                DescribeRole.Theorem)));

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, AssessedProvenance.FromLiterature(Source));
    private static DocumentBlock RepoDef(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, AssessedProvenance.FromRepo(Source));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Fn(string name, params Formula[] args) => new Formula.Apply(N(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AndTo(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Par(b));
    private static Formula PlusTo(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula f) => new Formula.Power(Par(f), D(2));
    private static Formula Inv(Formula f) => new Formula.Power(Par(f), new Formula.Negate(D(1)));
    private static Formula Adj(Formula f) => Fn("conjTranspose", f);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, Par(body));
    private static Formula Cases(Formula condition, Formula yes, Formula no) => Seq(N("if"), Sp, Par(condition), Sp, N("then"), Sp, Par(yes), Sp, N("else"), Sp, Par(no));
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula d) => Fn("Fin", d);
    private static Formula Prod(Formula a, Formula b) => Par(Seq(a, Times, b));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, b));
    private static Formula Lam(string name, Formula type, Formula body) => Par(Seq(F.Id(name), Colon, type, new Formula.LatexMacro(FormulaLatexMacro.Mapsto), body));
    private static Formula Code(Formula d) => Prod(FinOf(d), FinOf(d));
    private static Formula Mat(Formula a, Formula b) => Fn("Matrix", a, b, ComplexType);
    private static Formula CP(Formula a, Formula b) => Fn("CompletelyPositiveMap", Fn("CStarMatrix", a, a, ComplexType), Fn("CStarMatrix", b, b, ComplexType));
    private static Formula Map(Formula a, Formula b) => Fn("MatrixMap", a, b, ComplexType);
    private static Formula WithDP(Formula body) => Disp(All("d", NatType, All("p", RealType, body)));

    private static Formula Parameters(string name)
    {
        Formula d=F.Id("d"), p=F.Id("p"), d2=Sq(d), l1=Fn("lambda1",d,p), l4=Fn("lambda4",d,p);
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
    private static Formula PurificationFormula()
    {
        Formula d=F.Id("d"), a=F.Id("a"), b=F.Id("b");
        return Disp(All("d",NatType,All("a",FinOf(d),All("b",FinOf(d),EqTo(At(Fn("canonicalPurification",d),Pair(a,b)),Cases(EqTo(a,b),Inv(Fn("sqrt",d)),D(0)))))));
    }
    private static Formula PiFormula()
    {
        Formula d=F.Id("d"), psi=Fn("canonicalPurification",d);
        return Disp(All("d",NatType,EqTo(Fn("sourcePi",d),Fn("vecMulVec",psi,Fn("star",psi)))));
    }
    private static Formula QFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),pi=Fn("sourcePi",d);
        return WithDP(EqTo(Fn("sourceQ",d,p),Mul(Fn("sqrt",d),PlusTo(Mul(Fn("sqrt",Fr(Fn("lambda4",d,p),Sub(Sq(d),D(1)))),Sub(D(1),pi)),Mul(Fn("sqrt",Fn("lambda5",d,p)),pi)))));
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
        return WithDP(All("ij",Code(d),EqTo(Fn("sourceE",d,p,ij),Mul(Inv(Fn("sqrt",Fn("lambda4",d,p))),Sub(Fn("vecMulVec",basis,Fn("star",Fn("canonicalPurification",d))),Mul(Fn("sqrt",Fn("lambda5",d,p)),Adj(Fn("sourceB",d,p,ij))))))));
    }
    private static Formula RightFormula()
    {
        Formula d=F.Id("d"),x=F.Id("X"),a=F.Id("a"),b=F.Id("b"),j=F.Id("j");
        return Disp(All("d",NatType,All("X",Mat(Code(d),Code(d)),All("a",FinOf(d),All("b",FinOf(d),EqTo(At(Fn("rightTrace",d,x),a,b),SumOver("j",FinOf(d),At(x,Pair(a,j),Pair(b,j)))))))));
    }
    private static Formula NoiseFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),x=F.Id("X"),ij=F.Id("ij"),q=Fn("sourceQ",d,p),e=Fn("sourceE",d,p,ij);
        Formula first=Mul(Fn("lambda3",d,p),Mul(Fn("trace",x),D(1)));
        Formula second=Mul(Sub(Fn("lambda1",d,p),Fn("lambda3",d,p)),Fn("kronecker",Fn("partialTraceRight",Mul(Mul(q,x),q)),D(1)));
        Formula third=Mul(Fn("lambda2",d,p),SumOver("ij",Code(d),Mul(Mul(e,x),Adj(e))));
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
        Formula root=Fn("ofMatrixInverse",Fn("CFCsqrt",Fn("ofMatrix",Mul(Adj(c),c))));
        return WithDP(All("chi",new Formula.TypeArrow(FinOf(d),ComplexType),EqTo(Fn("sourcePolar",d,p,chi),Mul(c,Inv(root)))));
    }
    private static Formula ActionFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),x=F.Id("X");
        return Disp(All("a",N("FiniteIndex"),All("b",N("FiniteIndex"),All("f",CP(a,b),All("X",Mat(a,a),EqTo(Fn("matrixAction",f,x),Fn("ofMatrixInverse",At(f,Fn("ofMatrix",x)))))))));
    }
    private static Formula TNIFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),x=F.Id("X");
        Formula body=All("X",Mat(a,a),Imp(Fn("PosSemidef",x),LeTo(Fn("Re",Fn("trace",Fn("matrixAction",f,x))),Fn("Re",Fn("trace",x)))));
        return Disp(All("a",N("FiniteIndex"),All("b",N("FiniteIndex"),All("f",CP(a,b),IffTo(Fn("TraceNonincreasing",f),body)))));
    }
    private static Formula ChoiFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b"),f=F.Id("f"),swap=Fn("prodComm",b,a);
        return Disp(All("a",N("FiniteIndex"),All("b",N("FiniteIndex"),All("f",Map(a,b),EqTo(Fn("inputFirstChoi",f),Fn("reindex",swap,swap,Fn("choiMatrix",f)))))));
    }
    private static Formula FidelityFormula()
    {
        Formula d=F.Id("d"),f=F.Id("f"),psi=Fn("canonicalPurification",d);
        Formula output=Fn("kron",f,N("id"),Fn("vecMulVec",psi,Fn("star",psi)));
        return Disp(All("d",NatType,All("f",Map(FinOf(d),FinOf(d)),EqTo(Fn("entanglementFidelity",d,f),Fn("Re",Fn("dotProduct",Fn("star",psi),Fn("mulVec",output,psi)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula d=F.Id("d"),p=F.Id("p"),chi=F.Id("chi"),c=F.Id("C"),dec=F.Id("D"),i=F.Id("i");
        Formula actionC=Fn("matrixAction",c),actionD=Fn("matrixAction",dec),noise=Fn("sourceNoise",d,p),polar=Fn("sourcePolar",d,p,chi);
        Formula single=Lam("u",N("Unit"),polar);
        Formula rhs=Fn("entanglementFidelity",d,Fn("comp",Fn("rightTrace",d),Fn("comp",noise,Fn("ofKraus",single,single))));
        Formula lhs=Fn("entanglementFidelity",d,Fn("comp",actionD,Fn("comp",noise,actionC)));
        Formula competitors=All("C",CP(FinOf(d),Code(d)),All("D",CP(Code(d),FinOf(d)),Imp(Fn("TraceNonincreasing",c),Imp(Fn("TraceNonincreasing",dec),Imp(LeTo(Fn("rank",Fn("inputFirstChoi",actionC)),D(1)),LeTo(lhs,rhs))))));
        Formula body=All("d",NatType,Imp(LeTo(D(2),d),All("p",RealType,Imp(LtTo(D(0),p),Imp(LtTo(p,D(1)),All("chi",new Formula.TypeArrow(FinOf(d),ComplexType),Imp(EqTo(SumOver("i",FinOf(d),Fn("normSq",At(chi,i))),D(1)),competitors)))))));
        return Disp(IffTo(F.Id("claim"),body));
    }
}
