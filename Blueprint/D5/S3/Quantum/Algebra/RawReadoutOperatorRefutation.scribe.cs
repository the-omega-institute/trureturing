using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class RawReadoutOperatorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quaternion seminorm on H × M₃(R) satisfies all six conditions while hiding two nonzero raw operator defects.",
        H("Operator identities descend through the same seminorm kernel"),
        Blocks(
            Node("synthesis", "The raw synthesis operator", SynthesisFormula(),
                "Let V be a real vector space and m : V →ₗ[R] V →ₗ[R] V its actual bilinear multiplication. "
                + "Write xy = m(x,y). The parentheses are k c + a(bc) − b(ac), with k = ab − ba. No associativity is assumed in this definition.", DescribeRole.Definition),
            Node("projection", "The raw projection expression", ProjectionFormula(),
                "The same readout p defines q(x)=p(x)². The coefficient multiplies k T(c) in that order. Division is real division; no nonzero-denominator hypothesis is hidden in the definition.", DescribeRole.Definition),
            Node("Candidate", "The six conditions on the original algebra", CandidateFormula(),
                "B1 is carried by the bilinear type of m. B2 requires a nonnegative real-valued seminorm with absolute homogeneity and the triangle inequality. "
                + "E asserts a positive readout. N is exact multiplicativity. U_p uses one witness e for both readout unit equations. F quantifies over every raw c with the same witnesses a and b. "
                + "This packages chosen witnesses for the existential conditions; universal quantification over such witnesses preserves the original inference question.", DescribeRole.Definition),
            Node("claim", "The proposed exact lifting to the original domain", ClaimFormula(),
                "The assertion quantifies over all real vector spaces, bilinear multiplications, readouts and witnesses satisfying the six conditions. "
                + "It would place both the cubic identity and idempotence on the original vector space. The coefficient is 4q(ab−ba); in the model below it is 16. "
                + "Counterexample 5.7 distinguishes these equations from their valid equations on the readable quotient. This assertion records precisely the stronger inference it denies.", DescribeRole.Definition),
            Node("Certificate", "The complete simultaneous countermodel", EqualFormula(V("Certificate"), CertificateFormula()),
                "Here Raw = Quaternion R × Matrix (Fin 3) (Fin 3) R has its usual componentwise associative multiplication m and unit e=(1,I). "
                + "Set A=E₁₂+E₂₃, B=E₂₁+2E₃₂, K=diag(1,1,−2), i=(0,1,0,0), j=(0,0,1,0), and kH=(0,0,0,1). "
                + "The witnesses are a=(i,A), b=(j,B), k=ab−ba. Put p(h,X)=‖h‖, T=synthesis m a b, and P=projection m p a b. "
                + "N is the actual two-sided ideal ker(fst : Raw →ₐ[R] H). Thus membership in N is equivalent both to h=0 and to p(h,X)=0. "
                + "Let Q=Raw/N, write π for its quotient homomorphism, and let E : Q ≃ₐ[R] H be the algebra equivalence induced by the surjective first projection. "
                + "Define quotientT(x)=E⁻¹(4 kH E(x)) and quotientP(x)=x. The two intertwining equations prove that these are induced by the original T and P through this very quotient. "
                + "Every displayed conjunction is part of Certificate, including all original c, both nonzero defects at (0,I), the exact quotient identification, and both quotient polynomial laws.", DescribeRole.Definition),
            Node("raw_counterexample_certificate", "All clauses hold in one model", V("Certificate"),
                "Associativity gives T(c)=2kc. The commutator is (2kH,K); kH²=−1 and ‖kH‖=1. Hence p(Tc)=4p(c), proving F on every raw c. "
                + "Homogeneity, the triangle inequality and multiplicativity are inherited through the first projection from the quaternion norm. The actual product unit proves U_p and has readout one, proving E. "
                + "The full product calculation gives P(h,X)=(h,−K(KX)/4). Both polynomial defects therefore have first component zero for every c. "
                + "At (0,I), the cubic defect is diag(40,40,−128) in the matrix component and the idempotence defect is diag(5/16,5/16,2). Their (0,0) entries prove nonvanishing. "
                + "The first isomorphism theorem identifies the quotient by N with H, preserving multiplication and real scalars. Intertwining transports both operators; kH²=−1 proves the quotient cubic, and quotientP is the identity. "
                + "The result is the complete algebraic example of Counterexample 5.7; it asserts no physical realization or classification theorem.", DescribeRole.Theorem),
            Node("result", "The raw lifting inference is false", new Formula.Not(V("claim")),
                "Apply the proposed universal inference to the constructed model and its six-condition certificate. It makes the cubic defect vanish at (0,I), contradicting its nonzero matrix entry. "
                + "The certificate also proves that raw idempotence fails at the same point, while both defects vanish under the same readout and both equations hold on the quotient.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("raw-readout-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula R() => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula For(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] xs) => xs.Reverse().Aggregate((x,y) => new Formula.Logic(Par(y), FormulaLogicOperator.And, Par(x)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula EqualFormula(Formula a, Formula b) => Eq(a,b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula Scale(Formula a, Formula b) => Call("smul",a,b);
    private static Formula Pow(Formula a) => new Formula.Power(a,D(2));
    private static Formula Pair(Formula a, Formula b) => Call("pair",a,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Zero() => D(0);
    private static Formula T(Formula c) => Call("T",c);
    private static Formula P(Formula c) => Call("P",c);
    private static Formula Pi(Formula c) => Call("pi",c);
    private static Formula Read(Formula c) => Call("p",c);
    private static Formula Mem(Formula c) => Seq(c, Sp, InMacro, Sp,V("N"));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Iff,Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp,b);
    private static Formula Br(Formula x) => Seq(OpenBracket,x,CloseBracket);
    private static Formula Bil() => Call("Bilinear",V("R"),V("V"));
    private static Formula Kraw() => Sub(Call("m",V("a"),V("b")),Call("m",V("b"),V("a")));
    private static Formula Synth(Formula c) => Call("synthesis",V("m"),V("a"),V("b"),c);
    private static Formula Proj(Formula c) => Call("projection",V("m"),V("p"),V("a"),V("b"),c);
    private static Formula Space(Formula body) => For("V",V("Type"),Seq(Br(Call("AddCommGroup",V("V"))),Sp,Br(Call("Module",R(),V("V"))),Sp,body));
    private static Formula Inputs(Formula body, bool p, bool e) {
        foreach (string x in new[]{"b","a"}) body=For(x,V("V"),body);
        if(e) body=For("e",V("V"),body);
        if(p) body=For("p",Arr(V("V"),R()),body);
        return Space(For("m",Bil(),body));
    }
    private static Formula SynthesisFormula() {
        Formula c=V("c"), m=V("m"), a=V("a"), b=V("b");
        return Inputs(For("c",V("V"),Eq(Synth(c),Sub(Add(Call("m",Kraw(),c),Call("m",a,Call("m",b,c))),Call("m",b,Call("m",a,c))))),false,false);
    }
    private static Formula ProjectionFormula() => Inputs(For("c",V("V"),Eq(Proj(V("c")),
        Scale(Seq(Minus,new Formula.Fraction(D(1),Mul(D(2),Pow(Call("p",Kraw()))))),Call("m",Kraw(),Synth(V("c")))))),true,false);
    private static Formula CandidateBody() {
        Formula x=V("x"), y=V("y"), t=V("t"), c=V("c");
        return And(For("x",V("V"),Seq(Zero(),Sp,Leq,Sp,Read(x))),
            For("t",R(),For("x",V("V"),Eq(Read(Scale(t,x)),Mul(Call("abs",t),Read(x))))),
            For("x",V("V"),For("y",V("V"),Seq(Read(Add(x,y)),Sp,Leq,Sp,Add(Read(x),Read(y))))),
            Ex("x",V("V"),Seq(Zero(),Sp,Lt,Sp,Read(x))),
            For("x",V("V"),For("y",V("V"),Eq(Read(Call("m",x,y)),Mul(Read(x),Read(y))))),
            For("x",V("V"),Eq(Add(Read(Sub(Call("m",V("e"),x),x)),Read(Sub(Call("m",x,V("e")),x))),Zero())),
            For("c",V("V"),Imp(Eq(Read(Synth(c)),Zero()),Eq(Read(c),Zero()))));
    }
    private static Formula CandidateFormula() => Inputs(Eq(Call("Candidate",V("m"),V("p"),V("e"),V("a"),V("b")),CandidateBody()),true,true);
    private static Formula ClaimFormula() {
        Formula c=V("c"), cubic=For("c",V("V"),Eq(Synth(Synth(Synth(c))),Scale(Seq(Minus,Mul(D(4),Pow(Call("p",Kraw())))),Synth(c))));
        Formula idem=For("c",V("V"),Eq(Proj(Proj(c)),Proj(c)));
        return Eq(V("claim"),Inputs(Imp(Call("Candidate",V("m"),V("p"),V("e"),V("a"),V("b")),And(cubic,idem)),true,true));
    }
    private static Formula CertificateFormula() {
        Formula c=V("c"), x=V("x"), h=Call("fst",c), mat=Call("snd",c), witness=Pair(Zero(),V("I"));
        Formula cubic=Add(T(T(T(c))),Scale(D(1,6),T(c))), idem=Sub(P(P(c)),P(c));
        Formula cubicw=Add(T(T(T(witness))),Scale(D(1,6),T(witness))), idemw=Sub(P(P(witness)),P(witness));
        return And(Call("Candidate",V("m"),V("p"),D(1),V("a"),V("b")),
            For("c",V("Raw"),Eq(Pow(Read(c)),Call("normSq",h))),
            For("c",V("Raw"),Iff(Mem(c),Eq(h,Zero()))),
            For("c",V("Raw"),Iff(Mem(c),Eq(Read(c),Zero()))),
            Eq(V("k"),Pair(Scale(D(2),V("kH")),V("K"))), Eq(Pow(Read(V("k"))),D(4)),
            For("c",V("Raw"),Eq(T(c),Pair(Scale(D(4),Mul(V("kH"),h)),Scale(D(2),Mul(V("K"),mat))))),
            For("c",V("Raw"),Eq(P(c),Pair(h,Scale(Seq(Minus,new Formula.Fraction(D(1),D(4))),Mul(V("K"),Mul(V("K"),mat)))))),
            For("c",V("Raw"),And(Mem(cubic),Mem(idem))),
            Eq(cubicw,Pair(Zero(),Call("diagonal",D(4,0),D(4,0),Seq(Minus,D(1,2,8))))),
            Eq(idemw,Pair(Zero(),Call("diagonal",new Formula.Fraction(D(5),D(1,6)),new Formula.Fraction(D(5),D(1,6)),D(2)))),
            Ne(cubicw,Zero()),Ne(idemw,Zero()),
            For("c",V("Raw"),Eq(Call("E",Pi(c)),h)),
            For("c",V("Raw"),Eq(Pi(T(c)),Call("quotientT",Pi(c)))),
            For("c",V("Raw"),Eq(Pi(P(c)),Call("quotientP",Pi(c)))),
            For("x",V("Q"),Eq(Call("quotientT",Call("quotientT",Call("quotientT",x))),Scale(Seq(Minus,D(1,6)),Call("quotientT",x)))),
            For("x",V("Q"),Eq(Call("quotientP",Call("quotientP",x)),Call("quotientP",x))));
    }
}
