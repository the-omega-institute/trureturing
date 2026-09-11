using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class FiniteRecordCosineObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction.";
    private static Formula Integer => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strictly positive cosine error floor for every recovery of the finite-record channel.",
        H("Finite Record Cosine Obstruction"),
        Blocks(
            Item("coefficient_gamma_le_cosine", "Signed coefficient bound", CoefficientFormula(),
                "The norms of coefficients in each residue class form a zero-padded finite path. "
                + "Reindexing preserves the entire squared-norm mass, and the triangle inequality "
                + "bounds the complex autocorrelation by the adjacent products. The squared "
                + "zero-boundary averaging estimate and finite Cauchy-Schwarz bound each path. "
                + "Conjugation transports the result to negative gaps."),
            Item("finite_record_cosine_obstruction", "Positive recovery obstruction", ChannelFormula(),
                "The recording matrix followed by the displayed partial trace realizes one "
                + "canonical CPTP channel with the stated action on every complex matrix. "
                + "The all-density recovery lower bound in terms of the norm of gamma combines "
                + "with the signed coefficient estimate. Natural division equals the natural "
                + "floor of the nonnegative real quotient, whose integer floor is its integer "
                + "cast. The angle is strictly positive and at most pi over two, so this same "
                + "cosine margin is strictly positive."),
            Paragraph(Text("The coefficients are complex and may have arbitrary phases and internal "
                + "zeros. N may be zero, the selected gap may have either sign or exceed N in "
                + "absolute value, and all other labels may repeat. The type iota has an arbitrary "
                + "universe, a Fintype instance, and decidable equality.")),
            Paragraph(Text("Every sum over the integers denotes the literal Lean tsum. natDiv "
                + "denotes division in Nat; the fraction inside IntFloor is division in Real. "
                + "real and int denote the displayed scalar casts, and natAbs is integer "
                + "absolute value valued in Nat. The nonzero gap gives a nonzero absolute-value "
                + "denominator; its floor plus two is positive and nonzero.")),
            Paragraph(Text("QuantumChannel and DensityState are the canonical CPTP maps and all "
                + "density matrices from FiniteStateChannel. raw applies CStarMatrix.ofMatrix.symm "
                + "to the density state's value. act is the canonical map in matrix coordinates. "
                + "traceNorm is the real trace of the positive square root of the matrix Gram "
                + "matrix, and traceDistance is one half of that trace norm on the difference. "
                + "The supremum is the real sSup of the displayed range over all density states.")),
            Paragraph(Text("This obstruction is specific to the displayed finite-record channel "
                + "and a realized nonzero label gap. Unaffected degenerate subspaces remain "
                + "outside its obstruction claim. It does not assert an obstruction for arbitrary "
                + "encodings or physical realizations, nor a Hamiltonian, energy, locality, cost, "
                + "or recovery-algorithm statement. Cosine-bound attainment and the adjacent "
                + "uniform-coefficient example are separate statements.")))));

    private static DocumentBlock Item(string name, string title, Formula formula, string proof) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Exists(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Both(params Formula[] terms) => terms.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(Num(2)));
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula Conj(Formula a) => Call("conj", a);
    private static Formula SumOver(Formula k, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, domain), Sp, Grp(body));
    private static Formula Let(Formula body) => Seq(Operatorname, Grp(F.Id("let")), Sp, body, Semi, Sp);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Support(Formula c, Formula n) => All([Bound("k", Integer)],
        Implies(new Formula.Logic(Lt(F.Id("k"), Num(0)), FormulaLogicOperator.Or,
            Lt(Call("int", n), F.Id("k"))), Eqn(Apply(c, F.Id("k")), Num(0))));
    private static Formula Normalized(Formula c) =>
        Eqn(SumOver(F.Id("k"), Integer, Sq(Norm(Apply(c, F.Id("k"))))), Num(1));
    private static Formula Gamma(Formula c, Formula gap) => SumOver(F.Id("k"), Integer,
        Mul(Apply(c, Add(F.Id("k"), gap)), Conj(Apply(c, F.Id("k")))));
    private static Formula Cosine(Formula length) => Call("cos", Div(F.Id("pi"), Add(length, Num(2))));

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("N"), c = F.Id("c"), ell = F.Id("ell");
        return All([Bound("N", Nat), Bound("c", Arrow(Integer, Complex))],
            Implies(Both(Support(c, n), Normalized(c)), All([Bound("ell", Integer)],
                Implies(Ne(ell, Num(0)), Le(Norm(Gamma(c, ell)),
                    Cosine(Call("real", Call("natDiv", n, Call("natAbs", ell)))))))));
    }

    private static Formula ChannelFormula()
    {
        Formula type = F.Id("iota"), n = F.Id("N"), c = F.Id("c"), q = F.Id("q");
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a"), p = F.Id("p"), t = F.Id("t");
        Formula gamma = F.Id("gamma"), bigQ = F.Id("Q"), length = F.Id("L"), coord = F.Id("coord");
        Formula record = F.Id("record"), v = F.Id("V"), partial = F.Id("partialTrace"), lambda = F.Id("Lambda");
        Formula matrix = Call("Matrix", type, type, Complex), finL = Call("Fin", length);
        Formula product = Call("Product", type, finL), joint = F.Id("joint"), mat = F.Id("A");
        Formula channel = F.Id("C"), recovery = F.Id("R"), ell = F.Id("ell");
        Formula f = F.Id("f"), bound = F.Id("bound"), errors = F.Id("errors"), matrixErrors = F.Id("matrixErrors");
        Formula rho = F.Id("rho"), sigma = F.Id("sigma"), state = Call("DensityState", type);
        Formula definitions = Seq(
            Let(All([Bound("t", Integer)], Eqn(Apply(gamma, t), Gamma(c, t)))),
            Let(Eqn(bigQ, SumOver(i, type, Call("natAbs", Apply(q, i))))),
            Let(Eqn(length, Add(Add(n, Mul(Num(2), bigQ)), Num(1)))),
            Let(All([Bound("a", finL)], Eqn(Apply(coord, a), Sub(Call("int", Call("val", a)), Call("int", bigQ))))),
            Let(All([Bound("i", type), Bound("a", finL)],
                Eqn(Apply(record, i, a), Apply(c, Add(Apply(coord, a), Apply(q, i)))))),
            Let(All([Bound("p", product), Bound("j", type)], Eqn(Apply(v, p, j),
                Call("ite", Eqn(j, Call("fst", p)), Apply(record, Call("fst", p), Call("snd", p)), Num(0))))),
            Let(All([Bound("joint", Call("Matrix", product, product, Complex)), Bound("i", type), Bound("j", type)],
                Eqn(Apply(Apply(partial, joint), i, j), SumOver(a, finL,
                    Apply(joint, Call("pair", i, a), Call("pair", j, a)))))),
            Let(All([Bound("A", matrix)], Eqn(Apply(lambda, mat),
                Apply(partial, Mul(Mul(v, mat), Call("conjTranspose", v)))))));
        Formula raw = Call("raw", rho);
        Formula actualError = Call("traceDistance", Call("mapState", recovery, Call("mapState", channel, rho)), rho);
        Formula matrixError = Div(Call("traceNorm", Sub(Call("act", recovery, Apply(lambda, raw)), raw)), Num(2));
        Formula errorDefinitions = Seq(
            Let(Eqn(f, Call("IntFloor", Div(Call("real", n), Call("abs", Call("real", ell)))))),
            Let(Eqn(bound, Div(Sub(Num(1), Cosine(Call("real", f))), Num(2)))),
            Let(Eqn(errors, Call("range", Seq(Grp(rho, Sp, InMacro, Sp, state), Sp, Mapsto, Sp, actualError)))),
            Let(Eqn(matrixErrors, Call("range", Seq(Grp(rho, Sp, InMacro, Sp, state), Sp, Mapsto, Sp, matrixError)))));
        Formula conclusion = Both(Eqn(errors, matrixErrors),
            All([Bound("rho", state), Bound("sigma", state)], Both(
                Le(Num(0), Call("traceDistance", rho, sigma)), Le(Call("traceDistance", rho, sigma), Num(1)))),
            Call("Nonempty", errors), Call("BddAbove", errors), Le(bound, Call("sSup", errors)), Lt(Num(0), bound));
        Formula recoveryClaim = All([Bound("i", type), Bound("j", type), Bound("ell", Integer)],
            Implies(Ne(ell, Num(0)), Implies(Eqn(Sub(Apply(q, i), Apply(q, j)), ell),
                All([Bound("R", Call("QuantumChannel", type, type))], Seq(errorDefinitions, conclusion)))));
        Formula action = Both(All([Bound("A", matrix)], Eqn(Call("act", channel, mat), Apply(lambda, mat))),
            All([Bound("A", matrix), Bound("i", type), Bound("j", type)],
                Eqn(Apply(Apply(lambda, mat), i, j),
                    Mul(Apply(gamma, Sub(Apply(q, i), Apply(q, j))), Apply(mat, i, j)))), recoveryClaim);
        return All([Bound("iota", F.Id("Type")), Bound("fintype", Call("Fintype", type)),
            Bound("decidableEq", Call("DecidableEq", type)), Bound("N", Nat),
            Bound("c", Arrow(Integer, Complex)), Bound("q", Arrow(type, Integer))],
            Implies(Both(Support(c, n), Normalized(c)), Seq(definitions,
                Exists([Bound("C", Call("QuantumChannel", type, type))], action))));
    }
}
