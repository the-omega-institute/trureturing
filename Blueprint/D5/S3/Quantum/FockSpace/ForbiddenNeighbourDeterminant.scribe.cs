using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class ForbiddenNeighbourDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted forbidden-neighbour configurations, their Gram determinant, and quantum readout.",
        H("Forbidden Neighbour Determinant"),
        Blocks(
            Def("legalConfiguration", "legal-configuration", "The exclusion rule", LegalFormula(),
                "Coordinates are zero-based. A true Boolean means occupied; adjacent coordinates cannot both be occupied."),
            Def("legalConfigurationDecidable", "legal-configuration-decidable", "Decidable exclusion", DecidableFormula(),
                "The named instance decides the finite exclusion predicate and supplies the finite configuration subtype."),
            Def("occupationCount", "occupation-count", "Occupation number", CountFormula(),
                "Bool.toNat maps false to zero and true to one."),
            Def("forbiddenPartition", "forbidden-partition", "The configuration polynomial", PartitionFormula(),
                "The sum is over the legal subtype. Polynomial.X and Polynomial.C are the indeterminate and constant embedding. Coefficients use only powers and products of weights."),
            Def("lowerBidiagonal", "lower-bidiagonal", "The explicit bidiagonal matrix", BidiagonalFormula(),
                "Fin.mk carries the displayed index with its bound proof. Odd one-based weights form the diagonal; even one-based weights form the subdiagonal. The remaining entries are zero."),
            Describe.Lean(DescribeId.Create("gram-positive-semidefinite"), Handle("gramPosSemidef"),
                H("Gram positivity"), StatementSource.FromAuthor(GramFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This companion binds Mathlib Gram positivity for the explicit matrix. It includes singular matrices and does not need strictly positive weights."))), DescribeRole.Theorem),
            Def("gramEigenvalue", "gram-eigenvalue", "The Gram eigenvalues", EigenvalueFormula(),
                "The eigenvalues are Mathlib's real Hermitian eigenvalue list, including any zero eigenvalues."),
            Def("quantumState", "quantum-state", "Normalized configuration amplitudes", StateFormula(),
                "Both half exponents are real exponents. Nat.cast here denotes the real coercion. The complex vector uses the legal configurations as its coordinates."),
            Def("numberOperator", "number-operator", "The occupation observable", NumberFormula(),
                "Nat.cast here is the complex coercion. This diagonal matrix acts on the configuration space."),
            Def("tunnellingMatrix", "tunnelling-matrix", "Single-particle tunnelling", TunnellingFormula(),
                "The two blocks are indexed by Fin d. This single-particle space is distinct from the configuration space."),
            Describe.Lean(DescribeId.Create("forbidden-neighbour-determinant"), Handle("forbidden_neighbour_determinant"),
                H("Determinant realization and quantum readout"), StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/heilmannlieb1972monomerdimer")),
                Blocks(
                    Paragraph(Text("The parenthesized rows hold simultaneously. The weights are nonnegative, including zero; d is at least one. Matrix multiplication, scalar multiplication and polynomial evaluation have their displayed Mathlib meanings.")),
                    Paragraph(Text("The configuration recurrence is derived by splitting endpoint occupancy. A second endpoint expansion gives the path determinant recurrence, and interleaving the two parts of the explicit bidiagonal block matrix identifies the Gram determinant. Square roots cancel before the final polynomial coefficients.")),
                    Paragraph(Text("The negative-root clause is the weighted-path specialization of the Heilmann-Lieb zero principle (1972). The exact bidiagonal realization and normalized readout are the repository's explicit construction; the literature note attributes only the zero principle.")),
                    Paragraph(Text("The charpoly identity is an identity of real polynomials and applies at zero. The reciprocal evaluation formula is written for nonzero v; its polynomial continuation is the preceding identity, so totalized division at zero is never used to claim that formula.")),
                    Paragraph(Text("The symbol P in the conditional row is an arbitrary real polynomial. Substituting the actual Jensen polynomial requires the independent equality forbiddenPartition(w)=P. No RH assumption or such Jensen equality is asserted.")),
                    Paragraph(Text("The final row gives the two basis counts. Equality of partition polynomials does not assert a unitary equivalence of the complete physical systems. Nat.sub is natural truncated subtraction; every other division displayed below is in the real or complex field."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + name);
    private static DocumentBlock Def(string name, string id, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), Handle(name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] values)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        Formula function = Seq(Operatorname, Grp([.. parts]));
        return values.Length == 0 ? function : At(function, values);
    }
    private static Formula At(Formula function, params Formula[] values)
    {
        var items = new List<Formula>();
        foreach (var value in values)
        {
            if (items.Count > 0) items.AddRange([Comma, Sp]);
            items.Add(value);
        }
        return Seq(function, Parenthesized(Seq([.. items])));
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsIn(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula LeqOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula ImpliesOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Subtract(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Multiply(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Negative(Formula x) => new Formula.Negate(Parenthesized(x));
    private static Formula Inverse(Formula x) => new Formula.Fraction(D(1), x);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Twice(Formula n) => Multiply(D(2), n);
    private static Formula Edges(Formula d) => Call("Nat.sub", Twice(d), D(1));
    private static Formula BoolVector(Formula n) => Arrow(Fin(n), Call("Bool"));
    private static Formula Config(Formula n) => Seq(OpenBrace, Sp, F.Id("b"), Colon, Sp, BoolVector(n),
        Sp, Mid, Sp, Call("legalConfiguration", F.Id("b")), Sp, CloseBrace);
    private static Formula Weights(Formula n) => Arrow(Fin(n), Real());
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Lam(string name, Formula domain, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body));
    private static Formula SumOver(string name, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(F.Id(name), Colon, Sp, domain)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(F.Id(name), Colon, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Partition(Formula w) => Call("forbiddenPartition", w);
    private static Formula Count(Formula b) => Call("occupationCount", b);
    private static Formula Bit(Formula b, Formula i) => Call("Bool.toNat", At(b, i));
    private static Formula Lower(Formula w) => Call("lowerBidiagonal", w);
    private static Formula Gram(Formula w) => Multiply(Call("Matrix.transpose", Lower(w)), Lower(w));
    private static Formula Lift(Formula value) => Call("Matrix.map", value, Call("Polynomial.C"));
    private static Formula X() => Call("Polynomial.X");
    private static Formula Eigen(Formula w, Formula i) => Call("gramEigenvalue", w, i);
    private static Formula Eval(Formula p, Formula v) => Call("Polynomial.eval", v, p);
    private static Formula EvalComplex(Formula p, Formula v) =>
        Eval(Call("Polynomial.map", Call("Complex.ofRealHom"), p), v);
    private static Formula CastComplex(Formula r) => Call("Complex.ofReal", r);
    private static Formula Phase(Formula theta) => Call("Complex.exp", Multiply(CastComplex(theta), Call("Complex.I")));
    private static Formula State(Formula w, Formula r) => Call("quantumState", w, r);
    private static Formula Amplitude(Formula n, Formula w, Formula r, Formula b) =>
        Multiply(Power(r, new Formula.Fraction(Call("Nat.cast", Real(), Count(Val(b))), D(2))),
            ProductOver("i", Fin(n), Power(At(w, F.Id("i")),
                new Formula.Fraction(Call("Nat.cast", Real(), Bit(Val(b), F.Id("i"))), D(2)))));
    private static Formula PhaseReadout(Formula d, Formula w, Formula r, Formula theta) =>
        Call("dotProduct", Call("star", State(w, r)), Call("Matrix.mulVec",
            Call("NormedSpace.exp", Multiply(Multiply(CastComplex(theta), Call("Complex.I")),
                Call("numberOperator", Edges(d)))), State(w, r)));
    private static Formula PartitionRatio(Formula p, Formula r, Formula theta) => new Formula.Fraction(
        EvalComplex(p, Multiply(CastComplex(r), Phase(theta))), CastComplex(Eval(p, r)));
    private static Formula WithWeights(Formula body) =>
        All("d", Nat(), All("w", Weights(Edges(F.Id("d"))), body));

    private static Formula LegalFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        Formula exclusion = All("i", Fin(n), All("j", Fin(n),
            ImpliesOf(Equal(Add(Val(i), D(1)), Val(j)),
                Or(Equal(At(b, i), Call("false")), Equal(At(b, j), Call("false"))))));
        return Disp(All("n", Nat(), All("b", BoolVector(n),
            new Formula.Logic(Call("legalConfiguration", b), FormulaLogicOperator.Iff, exclusion))));
    }
    private static Formula DecidableFormula() => Disp(All("n", Nat(), All("b", BoolVector(F.Id("n")),
        Call("Decidable", Call("legalConfiguration", F.Id("b"))))));
    private static Formula CountFormula() => Disp(All("n", Nat(), All("b", BoolVector(F.Id("n")),
        Equal(Count(F.Id("b")), SumOver("i", Fin(F.Id("n")), Bit(F.Id("b"), F.Id("i")))))));
    private static Formula PartitionFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), b = F.Id("b"), i = F.Id("i");
        return Disp(All("n", Nat(), All("w", Weights(n), Equal(Partition(w), SumOver("b", Config(n),
            Multiply(Power(X(), Count(Val(b))), Call("Polynomial.C",
                ProductOver("i", Fin(n), Power(At(w, i), Bit(Val(b), i))))))))));
    }
    private static Formula BidiagonalFormula()
    {
        Formula d = F.Id("d"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        return Disp(WithWeights(All("i", Fin(d), All("j", Fin(d), Equal(At(Lower(w), i, j),
            Call("ite", Equal(i, j), Call("Real.sqrt", At(w, Call("Fin.mk", Twice(Val(i))))),
                Call("ite", Equal(Add(Val(j), D(1)), Val(i)),
                    Call("Real.sqrt", At(w, Call("Fin.mk", Add(Twice(Val(j)), D(1))))), D(0))))))));
    }
    private static Formula GramFormula() => Disp(WithWeights(Call("Matrix.PosSemidef", Gram(F.Id("w")))));
    private static Formula EigenvalueFormula() => Disp(WithWeights(Equal(Call("gramEigenvalue", F.Id("w")),
        Call("Matrix.IsHermitian.eigenvalues", Call("Matrix.PosSemidef.isHermitian", Call("gramPosSemidef", F.Id("w")))))));
    private static Formula StateFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), r = F.Id("r"), b = F.Id("b"), i = F.Id("i");
        return Disp(All("n", Nat(), All("w", Weights(n), All("r", Real(), All("b", Config(n),
            Equal(At(State(w, r), b), CastComplex(Multiply(Multiply(
                Inverse(Call("Real.sqrt", Eval(Partition(w), r))),
                Power(r, new Formula.Fraction(Call("Nat.cast", Real(), Count(Val(b))), D(2)))),
                ProductOver("i", Fin(n), Power(At(w, i),
                    new Formula.Fraction(Call("Nat.cast", Real(), Bit(Val(b), i)), D(2))))))))))));
    }
    private static Formula NumberFormula() => Disp(All("n", Nat(),
        Equal(Call("numberOperator", F.Id("n")), Call("Matrix.diagonal", Lam("b", Config(F.Id("n")),
            Call("Nat.cast", Complex(), Count(Val(F.Id("b")))))))));
    private static Formula TunnellingFormula() => Disp(WithWeights(Equal(Call("tunnellingMatrix", F.Id("w")),
        Call("Matrix.fromBlocks", D(0), Lower(F.Id("w")), Call("Matrix.transpose", Lower(F.Id("w"))), D(0)))));

    private static Formula MainFormula()
    {
        Formula d = F.Id("d"), w = F.Id("w"), i = F.Id("i"), z = F.Id("z"), t = F.Id("t");
        Formula v = F.Id("v"), n = F.Id("n"), u = F.Id("u"), r = F.Id("r"), theta = F.Id("theta");
        Formula b = F.Id("b"), p = F.Id("P");
        Formula nonnegative = All("i", Fin(Edges(d)), LeqOf(D(0), At(w, i)));
        Formula productIndex = Seq(i, Colon, Sp, Fin(d), Sp, Comma, Sp, Ne(Eigen(w, i), D(0)));
        Formula factorization = Equal(Partition(w), Seq(new Formula.Subscript(Prod, productIndex), Sp,
            Parenthesized(Add(D(1), Multiply(Call("Polynomial.C", Eigen(w, i)), X())))));
        Formula charpoly = Call("Matrix.charpoly", Call("tunnellingMatrix", w));
        Formula tail = Lam("i", Fin(Add(n, D(1))), At(u, Call("Fin.castSucc", i)));
        Formula tailTwo = Lam("i", Fin(n), At(u, Call("Fin.castSucc", Call("Fin.castSucc", i))));
        Formula endpoint = Call("Polynomial.C", At(u, Call("Fin.last", Add(n, D(1)))));
        Formula recurrence = All("n", Nat(), All("u", Weights(Add(n, D(2))), Equal(Partition(u),
            Add(Partition(tail), Multiply(Multiply(X(), endpoint), Partition(tailTwo))))));
        Formula basis = Call("Pi.single", b, D(1));
        Formula basisAction = All("b", Config(Edges(d)), Equal(
            Call("Matrix.mulVec", Call("numberOperator", Edges(d)), basis),
            Multiply(Call("Nat.cast", Complex(), Count(Val(b))), basis)));
        Formula basisExpansion = All("r", Real(), Equal(State(w, r),
            Multiply(Inverse(CastComplex(Call("Real.sqrt", Eval(Partition(w), r)))),
                SumOver("b", Config(Edges(d)), Multiply(CastComplex(Amplitude(Edges(d), w, r, b)), basis)))));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, d, Colon, Sp, Nat(), Comma, Sp, w, Colon, Sp, Weights(Edges(d)), Comma),
            Seq(Parenthesized(And(LeqOf(D(1), d), nonnegative)), Sp, Implies, Sp),
            Parenthesized(Equal(Partition(w), Call("Matrix.det", Add(D(1), Multiply(X(), Lift(Gram(w))))))),
            Parenthesized(Call("Matrix.PosSemidef", Gram(w))),
            Parenthesized(All("i", Fin(d), LeqOf(D(0), Eigen(w, i)))),
            Parenthesized(factorization),
            Parenthesized(All("z", Complex(), ImpliesOf(Equal(EvalComplex(Partition(w), z), D(0)),
                ExistsIn("t", Real(), And(Less(t, D(0)), And(Equal(z, CastComplex(t)),
                    ExistsIn("i", Fin(d), And(Less(D(0), Eigen(w, i)),
                        Equal(t, Negative(Inverse(Eigen(w, i)))))))))))),
            Parenthesized(Equal(charpoly, Call("Matrix.det", Subtract(
                Multiply(Power(X(), D(2)), D(1)), Lift(Gram(w)))))),
            Parenthesized(All("v", Real(), ImpliesOf(Ne(v, D(0)), Equal(Eval(charpoly, v),
                Multiply(Power(v, Twice(d)), Eval(Partition(w), Negative(Inverse(Power(v, D(2)))))))))),
            Parenthesized(recurrence),
            Parenthesized(basisExpansion),
            Parenthesized(All("r", Real(), ImpliesOf(Less(D(0), r), Equal(
                Call("dotProduct", Call("star", State(w, r)), State(w, r)), D(1))))),
            Parenthesized(basisAction),
            Parenthesized(All("r", Real(), All("theta", Real(), ImpliesOf(Less(D(0), r),
                Equal(PhaseReadout(d, w, r, theta), PartitionRatio(Partition(w), r, theta)))))),
            Parenthesized(All("P", Call("Polynomial", Real()), All("r", Real(), All("theta", Real(),
                ImpliesOf(And(Equal(Partition(w), p), Less(D(0), r)),
                    Equal(PhaseReadout(d, w, r, theta), PartitionRatio(p, r, theta))))))),
            Parenthesized(And(Equal(Call("Fintype.card", Config(Edges(d))), Call("Nat.fib", Add(Twice(d), D(1)))),
                Equal(Call("Fintype.card", Call("Sum", Fin(d), Fin(d))), Twice(d))))
        ]));
    }
}
