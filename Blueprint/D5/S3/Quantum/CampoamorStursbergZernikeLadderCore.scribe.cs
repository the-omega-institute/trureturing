using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CampoamorStursbergZernikeLadderCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/LieTheory/campoamor2026zernike");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial differential operators and the normal-order filtration for Zernike Hamiltonians.",
        H("Zernike operators and normal ordering"), Blocks(
            Paragraph(Text("Operators are complex linear endomorphisms of MvPolynomial (Fin 2) Complex. Multiplication is composition, 1 is the identity, and a centered dot denotes scalar multiplication. Polynomial coordinates 0 and 1 represent the source coordinates 1 and 2. All exponents and all subtractions between exponents are natural-number operations.")),
            Definition("q", QFormula(), "Equation (2.1): multiplication by the coordinate polynomial.", true),
            Definition("p", PFormula(), "Equation (2.1): minus the imaginary unit times the partial derivative.", true),
            Definition("dot", E(X("dot"), A(M(Qop(0), Pop(0)), M(Qop(1), Pop(1)))), "The ordered contraction of coordinates and momenta.", true),
            Definition("angularMomentum", E(X("angularMomentum"), Sub(M(Qop(0), Pop(1)), M(Qop(1), Pop(0)))), "Equation (2.5): angular momentum.", true),
            Definition("hamiltonian", HamiltonianFormula(), "Equation (2.3), for every natural N and every complex coefficient sequence.", true),
            Definition("monomial", MonomialFormula(), "The normal-ordered monomial has total degree a+b+c+d and grading a+b-c-d.", true),
            Definition("corrections", CorrectionsFormula(), "Equation (2.6): the complex span of normal-ordered monomials of positive degree at most 2N and grading zero.", true),
            Definition("IsSymmetry", SymmetryFormula(), "Equations (2.6) and (2.7): the difference from the kinetic term lies in the correction span, and the operator commutes with the Hamiltonian.", true),
            Definition("k1", E(X("k1"), X("angularMomentum")), "Equation (2.8): K1 is angular momentum.", true),
            Definition("k2", KFormula(false), "Equation (2.8): half the difference of the two symmetries.", true),
            Definition("k3", KFormula(true), "Equation (2.8): the commutator of angular momentum with k2.", true),
            Definition("phi1", PhiFormula(1), "Equation (5.1): the first factor of the structure function.", true),
            Definition("phi2", PhiFormula(2), "Equation (5.1): the second factor of the structure function.", true),
            Definition("phi", PhiFormula(0), "Equation (2.10): the ordered product of phi1 and phi2.", true),
            Definition("DivDiff.peval", EvalFormula(false), "Evaluation of the finite polynomial with coefficients gamma and exponents 1 through N.", false),
            Definition("DivDiff.divided", EvalFormula(true), "The polynomial divided difference, expressed as a finite geometric sum; no inverse or distinctness assumption is needed.", false),
            Theorem("Weyl.pp", WeylFormula(0), "The momenta commute.", true),
            Theorem("Weyl.qq", WeylFormula(1), "The coordinates commute.", true),
            Theorem("Weyl.pq", WeylFormula(2), "The coordinate and momentum commutator is the Heisenberg relation.", true),
            Theorem("DivDiff.peval_commute_left", EvalCommuteFormula(false), "An operator commuting with an argument commutes with its polynomial evaluation."),
            Theorem("DivDiff.divided_commute_left", EvalCommuteFormula(true), "Commutation with both arguments implies commutation with the divided difference."),
            Theorem("DivDiff.intertwine_divided", IntertwineFormula(), "Simultaneous intertwining of two arguments intertwines their divided difference."),
            Theorem("HamiltonianIdentity.symmetry", AlgebraIdentityFormula(false), "Shift relations make the divided-difference ladder commute with the polynomial Hamiltonian."),
            Theorem("ProductIdentity.factorization", AlgebraIdentityFormula(true), "The two ordered ladders multiply to the two factors obtained from the polynomial evaluations."),
            Theorem("Corrections.monotone", MonotoneFormula(), "Increasing N enlarges the correction span."),
            Theorem("Corrections.firstOrder_mem", FirstOrderFormula(), "Every coordinate-momentum product belongs to the correction span for N at least one."),
            Theorem("Corrections.dot_mem", DotMemFormula(), "The coordinate-momentum contraction belongs to the same span."),
            Theorem("Corrections.dot_pow_mul_mem", PowerFormula(false), "Multiplication by dot to the power r preserves grading zero and increases the positive total-degree bound by at most 2r."),
            Theorem("Corrections.C_pow_mul_mem", PowerFormula(true), "The same filtration estimate holds for any scalar multiple of angular momentum."))));

    private static DocumentBlock Definition(string name, Formula formula, string prose, bool source) => Describe.Lean(
        DescribeId.Create("zernike-core-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name.Split('.')[^1]),
        H(name), StatementSource.FromAuthor(Disp(formula)), source ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, Formula formula, string prose, bool literature = false) => Describe.Lean(
        DescribeId.Create("zernike-core-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name.Split('.')[^1]),
        H(name), StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula RingFamily(Formula body) => All("B", X("Type"), Seq(OpenBracket, Call("Ring", X("B")), CloseBracket, Sp, OpenBracket, Call("Algebra", Cplx, X("B")), CloseBracket, Comma, Sp, body));
    private static Formula NG(Formula body) => All("N", Nat, All("gamma", Coefficients, body));
    private static Formula Ops(string names, Formula type, Formula body)
    {
        foreach (string n in names.Split(' ').Reverse()) body = All(n, type, body);
        return body;
    }
    private static Formula QFormula() => All("i", Call("Fin", D(2)), E(Call("q", X("i")), Apply(Q("LinearMap", "mulLeft"), Cplx, Call("X", X("i")))));
    private static Formula PFormula() => All("i", Call("Fin", D(2)), E(Call("p", X("i")), S(MinusOf(Imag), Seq(Call("pderiv", X("i")), Dot, X("toLinearMap")))));
    private static Formula HamiltonianFormula() => NG(E(Call("hamiltonian", X("N"), X("gamma")), A(A(P(Pop(0), D(2)), P(Pop(1), D(2))), SumOver("k", Interval, S(Call("gamma", X("k")), P(X("dot"), X("k")))))));
    private static Formula MonomialFormula() => Ops("a b c d", Nat, E(Call("monomial", X("a"), X("b"), X("c"), X("d")), M(M(M(P(Qop(0), X("a")), P(Qop(1), X("b"))), P(Pop(0), X("c"))), P(Pop(1), X("d")))));
    private static Formula ExistsNat(string name, Formula body) => Seq(Exists, Sp, X(name), Colon, Sp, Nat, Comma, Sp, body);
    private static Formula CorrectionsFormula()
    {
        Formula degree = A(A(A(X("a"), X("b")), X("c")), X("d"));
        Formula body = And(E(A(X("a"), X("b")), A(X("c"), X("d"))), LeqOf(D(1), degree), LeqOf(degree, M(D(2), X("N"))), E(X("A"), Call("monomial", X("a"), X("b"), X("c"), X("d"))));
        foreach (string n in new[] { "d", "c", "b", "a" }) body = ExistsNat(n, body);
        Formula set = Seq(OpenBrace, X("A"), Colon, Sp, Operators, Sp, Bar, Sp, body, CloseBrace);
        return All("N", Nat, E(Call("corrections", X("N")), Apply(Q("Submodule", "span"), Cplx, set)));
    }
    private static Formula SymmetryFormula() => NG(Ops("T I", Operators, E(Call("IsSymmetry", X("N"), X("gamma"), X("T"), X("I")), Parenthesized(And(Mem(Sub(X("I"), X("T")), Call("corrections", X("N"))), E(Sub(M(X("I"), Call("hamiltonian", X("N"), X("gamma"))), M(Call("hamiltonian", X("N"), X("gamma")), X("I"))), D(0)))))));
    private static Formula KFormula(bool third) => Ops("I J", Operators, E(Call(third ? "k3" : "k2", X("I"), X("J")), third ? Sub(M(X("k1"), Call("k2", X("I"), X("J"))), M(Call("k2", X("I"), X("J")), X("k1"))) : S(Half, Sub(X("J"), X("I")))));
    private static Formula PhiFormula(int which)
    {
        Formula sum = SumOver("k", Interval, S(M(P(M(which == 1 ? D(2) : MinusOf(D(2)), Imag), X("k")), Call("gamma", X("k"))), P(which == 1 ? X("K") : Sub(X("K"), D(1)), X("k"))));
        Formula body = which == 0 ? M(Call("phi1", X("N"), X("gamma"), X("H"), X("K")), Call("phi2", X("N"), X("gamma"), X("H"), X("K"))) : which == 1 ? S(new Formula.Fraction(D(1), D(4)), Sub(X("H"), sum)) : Sub(X("H"), sum);
        return NG(Ops("H K", Operators, E(Call(which == 0 ? "phi" : which == 1 ? "phi1" : "phi2", X("N"), X("gamma"), X("H"), X("K")), body)));
    }
    private static Formula EvalFormula(bool divided)
    {
        Formula term = divided ? SumOver("j", Apply(Q("Finset", "range"), X("k")), M(P(X("s"), Sub(Sub(X("k"), D(1)), X("j"))), P(X("t"), X("j")))) : P(X("s"), X("k"));
        Formula rhs = SumOver("k", Interval, S(Call("gamma", X("k")), term));
        Formula lhs = divided ? Divided(X("s"), X("t")) : Eval(X("s"));
        return RingFamily(NG(Ops(divided ? "s t" : "s", X("B"), E(lhs, rhs))));
    }
    private static Formula WeylFormula(int which)
    {
        Formula pi = Call("p", X("i")), pj = Call("p", X("j")), qi = Call("q", X("i")), qj = Call("q", X("j"));
        Formula rhs = which == 2 ? Sub(M(qj, pi), S(Seq(X("if"), Sp, E(X("i"), X("j")), Sp, X("then"), Sp, Imag, Sp, X("else"), Sp, D(0)), Seq(D(1), Colon, Sp, Operators))) : which == 0 ? M(pj, pi) : M(qj, qi);
        return Ops("i j", Call("Fin", D(2)), E(which == 0 ? M(pi, pj) : which == 1 ? M(qi, qj) : M(pi, qj), rhs));
    }
    private static Formula EvalCommuteFormula(bool divided) => RingFamily(NG(Ops(divided ? "r s t" : "r s", X("B"), Imp(divided ? And(Call("Commute", X("r"), X("s")), Call("Commute", X("r"), X("t"))) : Call("Commute", X("r"), X("s")), Call("Commute", X("r"), divided ? Divided(X("s"), X("t")) : Eval(X("s")))))));
    private static Formula IntertwineFormula() => RingFamily(NG(Ops("r s t u v", X("B"), Imp(And(E(M(X("s"), X("r")), M(X("r"), X("u"))), E(M(X("t"), X("r")), M(X("r"), X("v")))), E(M(Divided(X("s"), X("t")), X("r")), M(X("r"), Divided(X("u"), X("v"))))))));
    private static Formula AlgebraIdentityFormula(bool product)
    {
        Formula alpha = X("alpha"), d = X("D"), a = X("A"), t = X("T"), r = X("R"), u = X("U"), v = X("V"), s = X("S");
        Formula shift = A(d, S(alpha, D(1))), e = A(a, S(alpha, D(1))), b = Sub(S(alpha, D(1)), a);
        Formula ladder = A(r, M(u, Divided(d, e))), h = A(t, Eval(d));
        Formula[] hypotheses = product ? new[] {
            Call("Commute", d, a), E(M(d, s), M(s, shift)), E(M(e, s), M(s, a)), E(M(d, v), M(v, d)), E(M(e, v), M(v, a)), E(M(d, t), M(t, shift)), E(M(a, t), M(t, a)), E(M(r, s), M(t, t)), E(M(r, v), M(t, Sub(d, b))), E(M(u, s), M(t, Sub(shift, a))), E(M(u, v), M(Sub(d, b), Sub(d, a)))
        } : new[] {
            Call("Commute", d, a), Call("Commute", d, u), E(M(d, t), M(t, shift)), E(M(a, t), M(t, a)), E(M(d, r), M(r, shift)), E(M(t, r), M(r, t)), E(M(t, u), Sub(M(u, t), S(alpha, r))), E(M(u, t), M(r, Sub(d, a)))
        };
        Formula conclusion = product ? E(M(ladder, A(s, M(v, Divided(d, b)))), M(Sub(h, Eval(a)), Sub(h, Eval(b)))) : E(M(h, ladder), M(ladder, h));
        return RingFamily(NG(All("alpha", Cplx, Ops(product ? "D A T R S U V" : "D A T R U", X("B"), Imp(And(hypotheses), conclusion)))));
    }
    private static Formula MonotoneFormula() => Ops("N M", Nat, Imp(LeqOf(X("N"), X("M")), LeqOf(Call("corrections", X("N")), Call("corrections", X("M")))));
    private static Formula FirstOrderFormula() => All("N", Nat, Imp(LeqOf(D(1), X("N")), Ops("i j", Call("Fin", D(2)), Mem(M(Call("q", X("i")), Call("p", X("j"))), Call("corrections", X("N"))))));
    private static Formula DotMemFormula() => All("N", Nat, Imp(LeqOf(D(1), X("N")), Mem(X("dot"), Call("corrections", X("N")))));
    private static Formula PowerFormula(bool angular) => Ops("N r", Nat, All("A", Operators, Imp(Mem(X("A"), Call("corrections", X("N"))), angular ? All("s", Cplx, Mem(M(P(S(X("s"), X("angularMomentum")), X("r")), X("A")), Call("corrections", A(X("N"), X("r"))))) : Mem(M(P(X("dot"), X("r")), X("A")), Call("corrections", A(X("N"), X("r")))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Apply(Formula function, params Formula[] args) => Seq(function, Parenthesized(Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray())));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Cplx => Seq(Mathbb, Grp(X("C")));
    private static Formula Operators => Apply(Q("Module", "End"), Cplx, Call("MvPolynomial", Call("Fin", D(2)), Cplx));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((a, i) => i == 0 ? new[] { Parenthesized(a) } : new[] { Sp, Land, Sp, Parenthesized(a) }).ToArray());
    private static Formula E(Formula a, Formula b) => Equal(a, b);
    private static Formula M(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula S(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula P(Formula a, Formula n) => new Formula.Power(Parenthesized(a), n);
    private static Formula A(Formula a, Formula b) => Add(a, b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a, b);
    private static Formula MinusOf(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula LeqOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Qop(byte i) => Call("q", D(i));
    private static Formula Pop(byte i) => Call("p", D(i));
    private static Formula Imag => Q("Complex", "I");
    private static Formula Coefficients => Arrow(Nat, Cplx);
    private static Formula SumOver(string v, Formula set, Formula body) => Seq(Sum, Underscore, Grp(Seq(X(v), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Interval => Apply(Q("Finset", "Icc"), D(1), X("N"));
    private static Formula Eval(Formula s) => Call("peval", X("N"), X("gamma"), s);
    private static Formula Divided(Formula s, Formula t) => Call("divided", X("N"), X("gamma"), s, t);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
}
