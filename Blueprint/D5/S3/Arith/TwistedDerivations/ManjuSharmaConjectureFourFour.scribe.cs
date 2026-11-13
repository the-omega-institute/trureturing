using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.TwistedDerivations;

internal sealed class ManjuSharmaConjectureFourFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Arith/manjusharma2024twisted");
    private static Formula N => F.Id("Nat");
    private static Formula Z => F.Id("Int");
    private static Formula Q => F.Id("Rat");
    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string a, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(a), t, body);
    private static Formula Ex(string a, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(a), t, body);
    private static Formula Call(string name, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. a]);
    private static Formula Both(params Formula[] a)
    {
        var value = a[^1];
        for (var i = a.Length - 2; i >= 0; i--) value = And(a[i], value);
        return value;
    }
    private static Formula Binds(Formula t, Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], t, body);
        return body;
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed adjugate denominator accepts a noninner derivation on the actual fourth cyclotomic integer ring.",
        H("Manju–Sharma Conjecture 4.4: the printed criterion fails"),
        Blocks(
            Paragraph(Text("The source is Manju and Sharma, Twisted Derivations in Algebraic Number Fields, "
                + "arXiv:2412.03507v2, Definition 2.1 and Section 4.2, Conjectures 4.3–4.4. "
                + "The original TeX reference in 4.4 is to 4.3. Its denominator is p to the e, "
                + "not the absolute determinant p to the power p to the e. The original version 1 "
                + "also prints that denominator. Adjugate means classical adjugate.")),
            Node("IsInner", "Integral innerness", InnerFormula(),
                "For every commutative ring O with its integer algebra structure, sigma and tau are integer-algebra "
                + "endomorphisms and D is integer-linear. The witness gamma belongs to O itself. "
                + "The equation is required for every x, exactly as in Definition 2.1."),
            Node("PrintedIntegralTest", "The literal printed integrality test", TestFormula(),
                "The arbitrary finite decidable index type iota indexes a square integer matrix and an integer column. "
                + "rat denotes coefficientwise inclusion into the rationals; inverse is rational inversion. "
                + "There must be an integer vector X equal coordinatewise to the rational vector "
                + "inverse(p^e) times adjugate(A)C. No integral solution of AX=C is assumed."),
            Node("claim", "The full universal source claim", Iff(V("claim"), ClaimFormula()),
                "All natural primes p and admissible k are quantified, with k unequal to one and p^k at least three. "
                + "The field K is a rational cyclotomic number field with a primitive p^k root zeta, and O is its "
                + "actual RingOfIntegers. The integral root z is toInteger(zeta). Every ordered integral power "
                + "basis pb with generator z and dimension p^(k-1)(p-1) is included. The two distinct algebra "
                + "endomorphisms preserve one and hence are nonzero. The representatives u and v lie below p^k, "
                + "are coprime to it and distinct; their root images and the factorization v=u+p^e*m are explicit. "
                + "Here e is nonnegative, m positive and p does not divide m. Every integer-linear D obeying "
                + "the twisted law on every pair x,y is included. A is literally leftMulMatrix of tau(z)-sigma(z) "
                + "in pb.basis and C is literally repr(D(z)); the formula repeats these definitions instead "
                + "of quantifying independent matrices. Both extra sufficient implications are retained."),
            Node("K4", "The actual fourth cyclotomic field", Eq(V("K4"), Call("CyclotomicField", F.D(4), Q)),
                "K4 is Mathlib's CyclotomicField 4 Rat with its field, number-field and rational cyclotomic instances."),
            Node("O4", "Its actual algebraic integer ring", Eq(V("O4"), Call("RingOfIntegers", V("K4"))),
                "O4 is the actual ring of integers, rather than an independently stipulated quadratic pair algebra."),
            Node("root", "A primitive fourth root", Eq(V("root"), Call("zeta", F.D(4), Q, V("K4"))),
                "The existing zeta_spec theorem proves that this chosen field element has exact order four."),
            Node("z", "The corresponding integral root", Eq(V("z"), Call("toInteger", V("root"))),
                "The integral primitive-root API supplies z in O4. The private z_sq proves z*z=-1."),
            Node("pb", "The existing integral power basis", Eq(V("pb"), Call("integralPowerBasis", V("root"))),
                "The existing integralPowerBasis_dim theorem computes dimension two. Its verified reindex "
                + "b is the ordered basis (1,z), not a replacement carrier or an assumed Gaussian identification."),
            Node("gaussianEquiv", "A proved generator-preserving Gaussian equivalence",
                Binds(Z, Eq(App(V("gaussianEquiv"), Call("gaussian", V("a"), V("c"))),
                    Add(Call("intCast", V("a")), Mul(Call("intCast", V("c")), V("z")))), "a", "c"),
                "Zsqrtd.lift constructs a ring homomorphism from GaussianInt using z*z=-1. Nonsquareness of "
                + "minus one gives injectivity by the upstream lift_injective theorem. Reconstruction using "
                + "the actual two-term integral basis gives surjectivity. Thus gaussianEquiv is an actual "
                + "integer-algebra equivalence and sends the Gaussian generator to z. This supplies the "
                + "multiplication and coordinate bridge; no identification is an extra hypothesis."),
            Node("tau", "Conjugation on the actual integer ring",
                All("x", V("O4"), Eq(App(V("tau"), V("x")),
                    App(V("gaussianEquiv"), Call("star", App(Call("symm", V("gaussianEquiv")), V("x")))))),
                "Conjugation is transported through the proved algebra equivalence. It is an integer-algebra "
                + "endomorphism and sends z to -z=z^3. The other twist is the identity, with u=1 and v=3."),
            Node("derivation", "The transported imaginary-coordinate map",
                All("x", V("O4"), Eq(App(V("derivation"), V("x")),
                    App(V("gaussianEquiv"), Call("gaussian", Call("im", App(Call("symm", V("gaussianEquiv")), V("x"))), F.D(0))))),
                "The Gaussian imaginary coordinate is an additive map and therefore integer-linear. Transport "
                + "gives D(a+bz)=b as an O4-valued integer-linear map. The all-input Gaussian product identity "
                + "D(xy)=D(x)conjugate(y)+xD(y) is proved by coordinate multiplication and transported. "
                + "Thus no generator-only check replaces the full twisted Leibniz law."),
            ResultNode())));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("manjusharma" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        name is "IsInner" or "PrintedIntegralTest" or "claim"
            ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock ResultNode() => Describe.Lean(
        DescribeId.Create("manjusharmaresult"), DeclarationHandle.Create(Prefix + "result"),
        H("The full printed Conjecture 4.4 is false"), StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
        AssessedProvenance.FromRepo(Source), Blocks(
            Paragraph(Text("Take p=2, k=2, n=4, u=1, v=3, e=1 and m=1. All unit, ordering, prime "
                + "and factorization conditions hold. In the actual ordered integral basis (1,z), "
                + "tau(z)-z=-2z, so multiplication has columns (0,-2) and (2,0). The actual matrix "
                + "is [[0,2],[-2,0]] and the actual vector of D(z)=1 is (1,0). Its classical adjugate "
                + "is [[0,-2],[2,0]], so the literal printed test gives (1/2)adj(A)C=(0,1), an integer vector. "
                + "The determinant is 4, consistent with the inherited conjectural value plus or minus 2^(2^1). "
                + "That determinant is a consequence of this matrix, never a premise of the claim or counterexample.")),
            Paragraph(Text("If an integral gamma=a+bz made D inner, evaluation at z would give "
                + "1=gamma*(-z)-z*gamma=2b-2az. The real coordinate forces 1=2b, impossible over the integers. "
                + "The proof pulls gamma back along the actual proved equivalence; it does not assume "
                + "existence of an integral solution. The full universal iff would force this noninner D "
                + "to be inner because its printed test holds. This contradicts the parity equation and "
                + "proves literally Not claim.")),
            Paragraph(Text("The counterexample negates the entire conjunction comprising the iff and both "
                + "additional sufficient assertions. It does not separately refute either sufficient assertion, "
                + "a corrected determinant-denominator statement, Conjecture 4.3 in general, or a corrigendum. "
                + "The quadratic classification is prior literature, not claimed as new mathematics. The "
                + "candidate admission basis is the full named external open-problem exception; no new "
                + "classification theorem or independent escape witness is claimed."))), DescribeRole.Theorem);

    private static Formula InnerFormula()
    {
        var o=V("O"); var s=V("sigma"); var t=V("tau"); var d=V("D"); var x=V("x"); var g=V("gamma");
        return All("O", V("Type"), Imp(Call("CommRing", o),
            Binds(Call("AlgHom", Z, o, o), All("D", Call("LinearMap", Z, o, o),
                Iff(Call("IsInner", s,t,d), Ex("gamma",o,All("x",o,
                    Eq(App(d,x),Sub(Mul(g,App(t,x)),Mul(App(s,x),g))))))), "sigma","tau")));
    }

    private static Formula TestFormula()
    {
        var i=V("i"); var j=V("iota"); var a=V("A"); var c=V("C"); var p=V("p"); var e=V("e");
        var value=Mul(Call("inverse",Pow(Call("rat",p),e)),
            App(Call("mulVec",Call("rat",Call("adjugate",a)),Call("rat",c)),i));
        return All("iota",V("Type"),Imp(Both(Call("Fintype",j),Call("DecidableEq",j)),
            Binds(N,All("A",Call("Matrix",j,j,Z),All("C",Call("Function",j,Z),
                Iff(Call("PrintedIntegralTest",p,e,a,c),Ex("X",Call("Function",j,Z),All("i",j,
                    Eq(value,Call("rat",App(V("X"),i)))))))),"p","e")));
    }

    private static Formula ClaimFormula()
    {
        var p=V("p"); var k=V("k"); var field=V("K"); var zeta=V("zeta"); var n=Pow(p,k);
        var o=Call("RingOfIntegers",field); var z=Call("toInteger",zeta); var pb=V("pb");
        var basis=Call("basis",pb); var s=V("sigma"); var t=V("tau"); var u=V("u"); var v=V("v");
        var e=V("e"); var m=V("m"); var d=V("D"); var i=V("i"); var x=V("x"); var y=V("y");
        var dim=Mul(Pow(p,Sub(k,F.D(1))),Sub(p,F.D(1))); var index=Call("Fin",dim);
        var a=Call("leftMulMatrix",basis,Sub(App(t,z),App(s,z)));
        var c=Call("repr",basis,App(d,z)); var inner=Call("IsInner",s,t,d);
        var answer=Both(Iff(inner,Call("PrintedIntegralTest",p,e,a,c)),
            Imp(All("i",index,Rel(Pow(Call("intCast",p),e),FormulaRelationOperator.Divides,App(c,i))),inner),
            Imp(All("i",index,Rel(Call("intCast",p),FormulaRelationOperator.Divides,App(c,i))),inner));
        var law=Binds(o,Eq(App(d,Mul(x,y)),Add(Mul(App(d,x),App(t,y)),Mul(App(s,x),App(d,y)))),"x","y");
        var reps=Both(Rel(u,FormulaRelationOperator.LessThan,n),Rel(v,FormulaRelationOperator.LessThan,n),
            Call("Coprime",u,n),Call("Coprime",v,n),Rel(u,FormulaRelationOperator.NotEqual,v),
            Eq(App(s,z),Pow(z,u)),Eq(App(t,z),Pow(z,v)),Rel(F.D(0),FormulaRelationOperator.LessThan,m),
            new Formula.Not(Rel(p,FormulaRelationOperator.Divides,m)),Eq(v,Add(u,Mul(Pow(p,e),m))));
        var tail=Binds(Call("AlgHom",Z,o,o),Imp(Rel(s,FormulaRelationOperator.NotEqual,t),
            Binds(N,Imp(reps,All("D",Call("LinearMap",Z,o,o),Imp(law,answer))),"u","v","e","m")),"sigma","tau");
        var bases=All("pb",Call("PowerBasis",Z,o),Imp(Both(Eq(Call("gen",pb),z),Eq(Call("dim",pb),dim)),tail));
        var fields=Both(Call("Field",field),Call("NumberField",field),Call("IsCyclotomicExtension",Call("singleton",n),Q,field),Call("NeZero",n));
        return Binds(N,Imp(Both(Call("Prime",p),Rel(k,FormulaRelationOperator.NotEqual,F.D(1)),
            Rel(F.D(3),FormulaRelationOperator.LessThanOrEqual,n)),All("K",V("Type"),Imp(fields,
                All("zeta",field,Imp(Call("IsPrimitiveRoot",zeta,n),bases))))),"p","k");
    }
}
