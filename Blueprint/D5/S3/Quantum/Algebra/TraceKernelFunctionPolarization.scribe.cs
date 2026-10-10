using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class TraceKernelFunctionPolarizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A trace-zero matrix function with an ambient polynomial representative, mixed bidegree law and simultaneous special-unitary invariance admits a normalized coefficient polarization.",
        H("Trace-Kernel Function Polarization"),
        Blocks(Describe.Lean(
            DescribeId.Create("trace-kernel-function-polarization"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Algebra/TraceKernelFunctionPolarization.trace_kernel_function_polarization"),
            H("Mixed polarization on the trace kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each choice of m,n,N in the statement, the notation uses the full matrix space M, its trace-zero subtype K, the disjoint slot set J and the entry-variable set V. The superscript H denotes conjugate transpose; SU and UnitaryGroup denote the corresponding complex matrix groups. The map C embeds complex coefficients in the indicated polynomial ring; evalTwo is polynomial substitution. The symbol delta(i,j) is one when i=j and zero otherwise; identity(N) is the identity matrix. Writing a polynomial applied to an entry assignment means polynomial evaluation, and compose(T,x) sends each slot j to T(x(j)). The multi-index ones assigns exponent one to every slot, including the empty multi-index when both degrees vanish. The symbols t are the slot-polynomial variables. MultilinearMap(C,J,M,C) means complex multilinear maps with one full-matrix input per slot in J.")),
                Paragraph(Math(NotationFormula())),
                Paragraph(Text(
                    "For every m,n ≥ 0 and N ≥ 1, an arbitrary ambient entry-polynomial "
                        + "representative of a trace-zero matrix function satisfying the stated "
                        + "mixed bidegree law and simultaneous SU(N) conjugation invariance yields "
                        + "a multilinear coefficient polarization on all matrix slots.")),
                Paragraph(Text(
                    "The squarefree coefficient is linear in each slot: the derivative chain rule removes one slot and expresses its coefficient as a linear sum of that slot’s entries. The two block factorials normalize the repeated inputs. The theorem recovers the original function on every repeated trace-zero pair, "
                        + "and records invariance under every linear map preserving the projected "
                        + "polynomial and under every unitary conjugation. It is a partial source "
                        + "bridge: the intrinsic representative correspondence and original source "
                        + "witness construction remain open.")),
                Paragraph(Text(
                    "The SU-circle reduction locally reuses the Tau Ceti contributors’ Apache 2.0 "
                        + "proof at revision d8fd630a6d98d0e5933f51cb0819ef09f28fa2b4. "
                        + "The full license, exact source provenance and retirement condition tied "
                        + "to this repository’s own Mathlib pin accompany the source."))),
            DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula EqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Par(value), Caret, Grp(exponent));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Cx => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula M => F.Id("M");
    private static Formula K => F.Id("K");
    private static Formula J => F.Id("J");
    private static Formula V => F.Id("V");
    private static Formula N => F.Id("N");
    private static Formula m => F.Id("m");
    private static Formula n => F.Id("n");
    private static Formula Triple(Formula a, Formula b, Formula c) => Seq(Open, a, Comma, b, Comma, c, Close);
    private static Formula Star(Formula value) => Seq(Par(value), Caret, Grp(F.Id("H")));
    private static Formula Conjugate(Formula u, Formula z) => Mul(Mul(u, z), Star(u));
    private static Formula Entry(Formula z, Formula i, Formula j) => At(z, i, j);
    private static Formula Cases(Formula yes, Formula condition, Formula no) => Seq(
        Begin, Grp(F.Id("cases")), yes, Amp, F.Text, Grp(F.Id("if")), Sp, condition,
        RowBreak, no, Amp, F.Text, Grp(F.Id("otherwise")), End, Grp(F.Id("cases")));
    private static Formula SumOver(string variable, Formula domain, Formula value) => Seq(
        Sum, Underscore, Grp(F.Id(variable), InMacro, Sp, domain), value);

    private static Formula NotationFormula()
    {
        Formula z = F.Id("Z"), w = F.Id("W"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k"),
            x = F.Id("x"), p = F.Id("P"), a = F.Id("A"), t = F.Id("t"), l = F.Id("l");
        Formula finN = Call("Fin", N);
        Formula variables = Seq(Seq(Call("Bool"), Times, Par(Seq(finN, Times, finN))));
        Formula traceZero = Seq(OpenBrace, z, InMacro, Sp, M, Bar, EqTo(Call("tr", z), D(0)), CloseBrace);
        Formula q = new Formula.Binary(z, FormulaBinaryOperator.Subtract,
            Mul(new Formula.Fraction(Call("tr", z), N), Call("identity", N)));
        Formula projectedVariable = new Formula.Binary(At(F.Id("X"), Triple(b, i, j)), FormulaBinaryOperator.Subtract,
            Mul(new Formula.Fraction(Call("delta", i, j), N),
                SumOver("k", finN, At(F.Id("X"), Triple(b, k, k)))));
        Formula entry = Cases(Entry(w, i, j), EqTo(b, Call("true")), Entry(z, i, j));
        Formula slotSum = Cases(
            SumOver("l", Call("Fin", n), Mul(Entry(At(x, Call("inr", l)), i, j), At(t, Call("inr", l)))),
            EqTo(b, Call("true")),
            SumOver("l", Call("Fin", m), Mul(Entry(At(x, Call("inl", l)), i, j), At(t, Call("inl", l)))));
        return Disp(Seq(
            EqTo(M, Call("Matrix", finN, finN, Cx)), Semi, Sp,
            EqTo(K, traceZero), Semi, Sp,
            EqTo(J, Call("Sum", Call("Fin", m), Call("Fin", n))), Semi, Sp,
            EqTo(V, variables), Semi, Sp,
            EqTo(Call("q", z), q), Semi, Sp,
            EqTo(At(Call("entries", z, w), Triple(b, i, j)), entry), Semi, Sp,
            EqTo(Call("Q", p), Call("evalTwo", Call("C"), Seq(Triple(b, i, j), Mapsto, Sp, projectedVariable), p)), Semi, Sp,
            EqTo(At(Call("S", x), Triple(b, i, j)), slotSum), Semi, Sp,
            EqTo(At(Call("repeat", z, w), Call("inl", i)), z), Semi, Sp,
            EqTo(At(Call("repeat", z, w), Call("inr", j)), w)));
    }

    private static Formula TheoremFormula()
    {
        Formula f = F.Id("f"), p = F.Id("P"), z = F.Id("Z"), w = F.Id("W"),
            u = F.Id("U"), x = F.Id("x"), a = F.Id("a"), b = F.Id("b"),
            linear = F.Id("T"), polarization = F.Id("F"), j = F.Id("j");
        Formula pairValue = At(f, z, w);
        Formula invariant = All("U", Call("SU", N), All("Z", K, All("W", K,
            EqTo(At(f, Conjugate(u, z), Conjugate(u, w)), pairValue))));
        Formula representative = All("Z", K, All("W", K,
            EqTo(At(p, Call("entries", z, w)), pairValue)));
        Formula degree = All("a", Cx, All("b", Cx, All("Z", K, All("W", K,
            EqTo(At(f, Mul(a, z), Mul(b, w)), Mul(Mul(Pow(a, m), Pow(b, n)), pairValue))))));
        Formula tupleSpace = new Formula.TypeArrow(J, M);
        Formula projected = Call("Q", p);
        Formula coefficient = new Formula.Fraction(
            Call("coeff", Call("ones", J), Call("evalTwo", Call("C"), Call("S", x), projected)),
            Mul(Call("factorial", m), Call("factorial", n)));
        Formula formula = All("x", tupleSpace, EqTo(At(polarization, x), coefficient));
        Formula recovery = All("Z", K, All("W", K,
            EqTo(At(polarization, Call("repeat", z, w)), pairValue)));
        Formula preserves = All("Z", M, All("W", M,
            EqTo(At(projected, Call("entries", At(linear, z), At(linear, w))),
                 At(projected, Call("entries", z, w)))));
        Formula linearCovariance = All("T", Call("LinearMap", Cx, M, M), Imp(preserves,
            All("x", tupleSpace, EqTo(At(polarization, Call("compose", linear, x)), At(polarization, x)))));
        Formula conjugatedTuple = Seq(j, Mapsto, Sp, Conjugate(u, At(x, j)));
        Formula unitary = All("U", Call("UnitaryGroup", N), All("x", tupleSpace,
            EqTo(At(polarization, Par(conjugatedTuple)), At(polarization, x))));
        Formula conclusion = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("F"), Call("MultilinearMap", Cx, J, M, Cx),
            And(formula, And(recovery, And(linearCovariance, unitary))));
        return Disp(All("m", Nat, All("n", Nat, All("N", Nat,
            Imp(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N),
                All("f", new Formula.TypeArrow(K, new Formula.TypeArrow(K, Cx)),
                    All("P", Call("MvPolynomial", V, Cx),
                        Imp(And(invariant, And(representative, degree)), conclusion))))))));
    }
}
