using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FaustSpectralInvariantsOddRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/faust2026spectralinvariants");
    public DocumentDefinition Create()
    {
        Formula r=V("R"), n=V("n"), m=V("m"), u=V("u"), v=V("V"), i=V("i"), j=V("j"), k=V("k");
        Formula odd=Add(Mul(D(2),m),D(1)), complex=C("Complex"), vars=Call("MvPolynomial",Fin(m),complex);
        Formula fm=RingBind(All("n",Nat(),All("V",Fn(Fin(n),r),All("i",Fin(n),All("j",Fin(n),Eqn(
            App(Call("floquetMatrix",n,v),i,j),If(Eqn(i,j),App(v,i),If(Adj(i,j,n),D(1),D(0)))))))));
        Formula fc=RingBind(All("n",Nat(),All("V",Fn(Fin(n),r),Eqn(Call("floquetCharPoly",n,v),
            Det(Sub(App(Q("Matrix","map"),Call("floquetMatrix",n,v),Q("Polynomial","C")),
                App(Q("HSMul","hSMul"),Q("Polynomial","X"),D(1))))))));
        Formula index=Seq(Langle,Val(j),Comma,Sp,Seq(Dot,Dot,Dot),Rangle);
        Formula reverse=Seq(Langle,Sub(Mul(D(2),m),Val(j)),Comma,Sp,Seq(Dot,Dot,Dot),Rangle);
        Formula specialized=All("m",Nat(),All("j",Fin(odd),Eqn(Call("specializedPotential",m,j),
            If(new Formula.Relation(Val(j),FormulaRelationOperator.LessThan,m),App(Q("MvPolynomial","X"),index),
                If(Eqn(Val(j),m),D(0),MinusOf(App(Q("MvPolynomial","X"),reverse)))))));
        Formula zeta=All("m",Nat(),Eqn(Call("zeta",m),Sub(Call("floquetCharPoly",odd,Call("specializedPotential",m)),
            Call("floquetCharPoly",odd,Parenthesized(Seq(D(0),Colon,Sp,Fn(Fin(odd),vars)))))));
        Formula pp=All("m",Nat(),All("k",Nat(),Eqn(Call("pPrime",m,k),Mul(
            new Formula.Power(Parenthesized(MinusOf(D(1))),Add(odd,k)),
            App(Q("Polynomial","coeff"),Call("zeta",m),Sub(odd,Mul(D(2),k)))))));
        Formula variety=All("m",Nat(),All("u",Fn(Fin(m),complex),Eqn(Call("InVariety",m,u),Parenthesized(
            All("k",Nat(),Imp(new Formula.Relation(k,FormulaRelationOperator.MemberOf,App(Q("Finset","Icc"),D(1),m)),
                Eqn(App(Q("MvPolynomial","eval"),u,Call("pPrime",m,k)),D(0))))))));
        Formula jac=All("m",Nat(),All("u",Fn(Fin(m),complex),All("k",Fin(m),All("j",Fin(m),Eqn(
            App(Call("jacobianAt",m,u),k,j),App(Q("MvPolynomial","eval"),u,
                App(Q("MvPolynomial","pderiv"),j,Call("pPrime",m,Add(Val(k),D(1))))))))));
        Formula regular=All("m",Nat(),All("u",Fn(Fin(m),complex),Eqn(Call("IsRegularPoint",m,u),
            Ne(Det(Call("jacobianAt",m,u)),D(0)))));
        return DocumentDefinition.Create(ScribeNode.Create("A nonzero singular point for the odd clause of Conjecture 3.",
            H("A repeated five-site potential refutes odd-period regularity"),Blocks(
                Paragraph(Text("M. Faust, L. Friedman, G. O’Malley, R. Ramos and A. Sharma, Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian, arXiv:2602.08304v1. All Fin indices below are zero-based; q=2m+1 and generator k+1 corresponds to source p′ₖ₊₁. Proof components of Fin indices are suppressed by ellipses. Natural subtraction is truncated subtraction and Nat.mod is remainder. Section 3, p. 7: “we are always referring to the multiplicity of a point according to the defining ideal (not with respect to the radical).”")),
                Node("matrix","Floquet matrix at z=1","floquetMatrix",fm,"Section 2, p. 3: “Thus, from here on we write L_V in place of L_V(1)”. The diagonal is V and each cyclic edge has coefficient one.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("characteristic","The characteristic polynomial","floquetCharPoly",fc,"Section 2, p. 3: “Let D_V(λ) denote the characteristic polynomial of L_V”. The determinant uses L_V−λI, exactly with this sign.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("potential","Antisymmetric specialization","specializedPotential",specialized,"Section 4, p. 8: “For odd n= 2m+1, this yields a potential function of the form (u₁, …, uₘ, 0, −uₘ, …, −u₁).” The source sites 1 through 2m+1 correspond to Fin indices 0 through 2m.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("zeta","Difference from the free polynomial","zeta",zeta,"Section 2 defines ζ_V := D_V(λ) − D_𝟎(λ). Here V is the specialized potential.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("generators","Generators of I′","pPrime",pp,"Section 4 defines p′ₖ := (−1)ⁿ⁺ᵏ ζ_U[λⁿ⁻²ᵏ] and I′ := ⟨p′₁, …, p′ₘ⟩. The expression defines pPrime for every natural k; only k=1 through m generate I′.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("variety","The common zero set","InVariety",variety,"Every generator with index in the closed interval from 1 to m vanishes at u.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("jacobian","Jacobian of the generators","jacobianAt",jac,"Rows index generators from pPrime m 1 to pPrime m m; columns index the m coordinates. Entries are evaluated formal partial derivatives.",DescribeRole.Definition,AssessedProvenance.FromRepo(Source)),
                Node("regular","Jacobian regularity","IsRegularPoint",regular,"The proposition uses the Jacobian determinant criterion, with no separate local-algebra multiplicity theorem.",DescribeRole.Definition,AssessedProvenance.FromRepo(Source)),
                Node("claim","Conjecture 3, odd clause","claim",Eqn(Call("claim"),Parenthesized(ClaimBody())),"Conjecture 3, p. 11: “When q is odd, then V(I′) has only regular nonzero points, and when it is an even number greater than 6 there is a single singular point, up to symmetry, of multiplicity 2^{q/2−2}. Moreover, the multiplicity at 𝟎 is 2^{⌊q/2⌋}.” The quantifier ranges over every odd q=2m+1>3. Period means a period, without a least-period requirement.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source)),
                Node("result","Refutation at q=15","result",Seq(Neg,Sp,Parenthesized(ClaimBody())),"Choose a with a²=1−2i and u=(a,ia,0,−ia,−a,a,ia). The corresponding fifteen-site potential repeats (a,ia,0,−ia,−a) three times. Its five-step transfer trace equals the free trace, and determinant-one evolution preserves that equality for the cube, so every generator vanishes. Cyclic shift by five preserves the potential and the characteristic coefficients. Differentiation and antisymmetric specialization identify Jacobian columns 0 and 5, forcing zero determinant. The coordinate a is nonzero. This refutes the stated odd clause; the least-period variant, the even clause and origin multiplicity are not settled here.",DescribeRole.Theorem,AssessedProvenance.FromRepo(Source)))));
    }
    private static Formula ClaimBody() => All("m",Nat(),Imp(Leq(D(2),V("m")),All("u",Fn(Fin(V("m")),C("Complex")),
        Imp(Ne(V("u"),D(0)),Imp(Call("InVariety",V("m"),V("u")),Call("IsRegularPoint",V("m"),V("u")))))));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Leq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static DocumentBlock Node(string id,string title,string name,Formula f,string prose,DescribeRole role,AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("faust-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance,Blocks(Paragraph(Text(prose))),role);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Q(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? C(s) : App(C(s), a);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MinusOf(Formula a) => new Formula.Negate(Parenthesized(a));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => C("Nat");
    private static Formula Val(Formula i) => Call("val", i);
    private static Formula Mod(Formula a, Formula n) => App(Q("Nat", "mod"), a, n);
    private static Formula Adj(Formula i, Formula j, Formula n) => new Formula.Logic(
        Eqn(Mod(Add(Val(i), D(1)), n), Val(j)), FormulaLogicOperator.Or,
        Eqn(Mod(Add(Val(j), D(1)), n), Val(i)));
    private static Formula If(Formula h, Formula a, Formula b) => Seq(C("if"), Sp, Parenthesized(h), Sp, C("then"), Sp, a, Sp, C("else"), Sp, b);
    private static Formula Det(Formula a) => App(Q("Matrix", "det"), a);
    private static Formula RingBind(Formula f) => All("R", C("Type"), Seq(OpenBracket, Call("CommRing", V("R")), CloseBracket, Sp, f));
}
