using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.TwistedDerivations;

internal sealed class ManjuSharmaConjectureFiveTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quad/manjusharma2024twisted");
    private static Formula V(string name) => F.Id(name);
    private static Formula N => V("Nat");
    private static Formula Z => V("Int");
    private static Formula Q => V("Rat");
    private static Formula Call(string name, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. a]);
    private static Formula App(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string a, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(a), t, body);
    private static Formula Ex(string a, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(a), t, body);
    private static Formula Both(params Formula[] a)
    {
        var result = a[^1];
        for (var i = a.Length - 2; i >= 0; i--) result = And(a[i], result);
        return result;
    }
    private static Formula Binds(Formula t, Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], t, body);
        return body;
    }
    private static Formula Law(Formula o, Formula s, Formula t, Formula d) => Binds(o,
        Eq(App(d, Mul(V("x"), V("y"))), Add(Mul(App(d, V("x")), App(t, V("y"))),
            Mul(App(s, V("x")), App(d, V("y"))))), "x", "y");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal adjugate test in Conjecture 5.2 misses a nonzero outer class on the actual fourth cyclotomic integer ring.",
        H("Manju–Sharma Conjecture 5.2: the full outer criterion fails"),
        Blocks(
            Paragraph(Text("The source is Manju and Sharma, Twisted Derivations in Algebraic Number Fields, "
                + "arXiv:2412.03507v2, Section 5.2, Conjecture 5.2, TeX lines 2240–2242. Its inherited "
                + "hypotheses are those of Conjecture 4.3, rather than the conjectural determinant conclusion. "
                + "Definition 2.1 defines outer derivations as quotient classes; the Remark at TeX lines "
                + "156–158 identifies non-inner representatives with nonzero classes. The criterion and "
                + "the universal strict inclusion are retained together.")),
            Node("derivations", "All twisted derivations", DerivationsFormula(),
                "For any commutative ring O, sigma and tau are unital integer-algebra endomorphisms. "
                + "The carrier consists of integer-linear maps satisfying the displayed identity for every x and y. "
                + "Zero, addition and integer scalar multiplication preserve that identity."),
            Node("inner", "The submodule of integral inner derivations", InnerFormula(),
                "The ambient module is the actual module of twisted derivations. Membership requires a single "
                + "gamma in O valid for every input, exactly the reused IsInner definition. A multiplier only "
                + "in the fraction field is insufficient. Zero, sums and integer multiples have integral multipliers."),
            Node("outerClass", "The quotient class of a derivation", OuterFormula(),
                "The map is the canonical linear quotient map Der to Der/Inn. Mathlib's mk_eq_zero theorem "
                + "gives class(D)=0 if and only if D belongs to Inn. Consequently class(D) is nonzero if and "
                + "only if the representative is non-inner; the proof uses this exact equivalence."),
            Node("claim", "The entire universal conjunction", Iff(V("claim"), ClaimFormula()),
                "Every rational prime p is included, with k a natural number unequal to one and p^k at least "
                + "three. K is an actual rational cyclotomic number field, O its full RingOfIntegers, z the "
                + "integral primitive root, and pb every integral power basis with generator z and dimension "
                + "p^(k-1)(p-1). Its basis_eq_pow field fixes the source ordering (1,z,...). Unital maps "
                + "of this nontrivial ring are nonzero. The unit representatives u and v satisfy 1<=u,v<p^k, "
                + "coprimality and distinctness, and give the actual root images. The exponent e is nonnegative; "
                + "m is positive and prime to p. The disjunction includes the positive source factorization in "
                + "either order. A is always the actual left multiplication matrix of tau(z)-sigma(z), and C "
                + "is the actual coordinate column of D(z). PrintedIntegralTest is reused without changing "
                + "its literal p^e denominator or its classical adjugate. The second conjunct asserts that Inn "
                + "is a proper submodule of the full derivation module, together with its stated nonzero-class "
                + "interpretation, for every admissible pair, independently of any chosen D."),
            Paragraph(Text("To compare the two source orders, exchange sigma,u with tau,v. Commutativity and "
                + "the product law applied to y,x give the same space of derivations. Replacing the integral "
                + "inner multiplier gamma by -gamma leaves the inner submodule unchanged. The actual matrix "
                + "becomes -A while C is unchanged. The existing adjugate_smul identity gives "
                + "Adj(-A)=(-1)^(N-1)Adj(A), so the rational test vector only changes by an integer sign. "
                + "Integrality, its negation and the strict inclusion are therefore unchanged. This explains "
                + "the explicit two-order quantifier without imposing the determinant conjecture or excluding "
                + "a reversed distinct pair.")),
            Describe.Lean(DescribeId.Create("manjusharmafivetworesult"), DeclarationHandle.Create(Prefix + "result"),
                H("The full printed Conjecture 5.2 is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Reuse the actual fourth cyclotomic field and its full ring of integers "
                        + "from ManjuSharmaConjectureFourFour. Take p=k=2, u=1, v=3, e=m=1, sigma the identity, "
                        + "tau conjugation, and the ordered integral basis (1,z), z^2=-1. The existing pointed "
                        + "Gaussian algebra equivalence defines the genuine integer-linear derivation "
                        + "D(a+bz)=b and proves its twisted law on every pair of algebraic integers.")),
                    Paragraph(Text("The existing derivation_not_inner theorem gives non-innerness over the full "
                        + "integer ring, hence the quotient class is nonzero by mk_eq_zero. The existing printed_test "
                        + "uses the actual matrix A=[[0,2],[-2,0]], C=(1,0), Adj(A)=[[0,-2],[2,0]], and "
                        + "(1/2)Adj(A)C=(0,1). Thus the printed test is integral despite the nonzero outer class. "
                        + "The forward direction of the conjectured biconditional says that this same vector "
                        + "is not integral, a contradiction. Primitive-root power injectivity verifies distinctness "
                        + "of the twists from their root images.")),
                    Paragraph(Text("This refutes the entire conjunction by falsifying its criterion. It does not "
                        + "refute the universal strict-inclusion assertion separately, nor a criterion with a "
                        + "corrected denominator. In the concrete fourth-root case the exhibited nonzero quotient "
                        + "class supports existence of outer derivations. Conjecture 4.3 is never assumed. "
                        + "The mathematics of the actual cyclotomic counterexample is reused from the existing "
                        + "Conjecture 4.4 result; the conclusion here concerns the distinct full printed Conjecture 5.2."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("manjusharmafivetwo" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DerivationsFormula()
    {
        var o = V("O"); var s = V("sigma"); var t = V("tau"); var d = V("D");
        return All("O", V("Type"), Imp(Call("CommRing", o), Binds(Call("AlgHom", Z, o, o),
            All("D", Call("LinearMap", Z, o, o), Iff(Call("member", d, Call("derivations", s,t)),
                Law(o,s,t,d))), "sigma", "tau")));
    }
    private static Formula InnerFormula()
    {
        var o=V("O"); var s=V("sigma"); var t=V("tau"); var d=V("D");
        return All("O",V("Type"),Imp(Call("CommRing",o),Binds(Call("AlgHom",Z,o,o),
            All("D",Call("derivations",s,t),Iff(Call("member",d,Call("inner",s,t)),
                Call("IsInner",s,t,Call("val",d)))),"sigma","tau")));
    }
    private static Formula OuterFormula()
    {
        var o=V("O"); var s=V("sigma"); var t=V("tau"); var d=V("D");
        return All("O",V("Type"),Imp(Call("CommRing",o),Binds(Call("AlgHom",Z,o,o),
            All("D",Call("derivations",s,t),Eq(Call("outerClass",s,t,d),
                App(Call("mkQ",Call("inner",s,t)),d))),"sigma","tau")));
    }
    private static Formula ClaimFormula()
    {
        var p=V("p"); var k=V("k"); var field=V("K"); var zeta=V("zeta"); var n=Pow(p,k);
        var o=Call("RingOfIntegers",field); var z=Call("toInteger",zeta); var pb=V("pb");
        var basis=Call("basis",pb); var s=V("sigma"); var t=V("tau"); var u=V("u"); var v=V("v");
        var e=V("e"); var m=V("m"); var d=V("D");
        var dim=Mul(Pow(p,Sub(k,F.D(1))),Sub(p,F.D(1)));
        var a=Call("leftMulMatrix",basis,Sub(App(t,z),App(s,z)));
        var c=Call("repr",basis,App(Call("val",d),z));
        var nonzero=Ne(Call("outerClass",s,t,d),F.D(0));
        var answer=Both(All("D",Call("derivations",s,t),
                Iff(nonzero,new Formula.Not(Call("PrintedIntegralTest",p,e,a,c)))),
            Rel(Call("inner",s,t),FormulaRelationOperator.LessThan,Call("top",Call("derivations",s,t))),
            Ex("D",Call("derivations",s,t),nonzero));
        var reps=Both(Rel(F.D(0),FormulaRelationOperator.LessThan,u),Rel(F.D(0),FormulaRelationOperator.LessThan,v),
            Rel(u,FormulaRelationOperator.LessThan,n),Rel(v,FormulaRelationOperator.LessThan,n),
            Call("Coprime",u,n),Call("Coprime",v,n),Ne(u,v),Eq(App(s,z),Pow(z,u)),Eq(App(t,z),Pow(z,v)),
            Rel(F.D(0),FormulaRelationOperator.LessThan,m),new Formula.Not(Rel(p,FormulaRelationOperator.Divides,m)),
            Or(Eq(v,Add(u,Mul(Pow(p,e),m))),Eq(u,Add(v,Mul(Pow(p,e),m)))));
        var tail=Binds(Call("AlgHom",Z,o,o),Imp(Ne(s,t),Binds(N,Imp(reps,answer),"u","v","e","m")),"sigma","tau");
        var bases=All("pb",Call("PowerBasis",Z,o),Imp(Both(Eq(Call("gen",pb),z),Eq(Call("dim",pb),dim)),tail));
        var fields=Both(Call("Field",field),Call("NumberField",field),
            Call("IsCyclotomicExtension",Call("singleton",n),Q,field),Call("NeZero",n));
        return Binds(N,Imp(Both(Call("Prime",p),Ne(k,F.D(1)),Rel(F.D(3),FormulaRelationOperator.LessThanOrEqual,n)),
            All("K",V("Type"),Imp(fields,All("zeta",field,Imp(Call("IsPrimitiveRoot",zeta,n),bases))))),"p","k");
    }
}
