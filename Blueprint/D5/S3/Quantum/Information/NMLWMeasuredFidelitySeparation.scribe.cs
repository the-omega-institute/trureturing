using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class NMLWMeasuredFidelitySeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quantum/nuradha2025multivariate");
    private const string Question = "Remark 5.45, page 34: \"Furthermore, it is interesting to determine whether there exists a tuple of states for which F_M(ρ_1, …, ρ_r) > F_U(ρ_1, …, ρ_r)—we leave this as an open question.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three qubit states have measured average pairwise fidelity above the Uhlmann average.",
        H("Strict separation of measured and Uhlmann average fidelities"),
        Blocks(
            Node("uhlmann", "Uhlmann root fidelity", UhlmannFormula(),
                "Proposition 3.1, page 9: \"F(ρ, σ) := ‖√ρ √σ‖₁\". Here CFC.sqrt is the positive matrix square root and D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm is the matrix trace norm. The index type n is finite and has decidable equality.", AssessedProvenance.FromLiterature(Source)),
            Node("FU", "Average pairwise Uhlmann fidelity", AverageFormula(false),
                "Equation (5.13), page 18: \"F_U(ρ_1, …, ρ_r) := (2/(r(r−1))) Σ_{i<j} F(ρ_i, ρ_j).\" Finset.Ioi i selects exactly the larger indices, so each unordered pair appears once. All normalization arithmetic is real. CStarMatrix.ofMatrix.symm converts the positive trace-one DensityState values to ordinary matrices.", AssessedProvenance.FromLiterature(Source)),
            Node("FM", "Measured average pairwise fidelity", AverageFormula(true),
                "Definition 5.40, page 32: \"F_M(ρ_1, …, ρ_r) := (2/(r(r−1))) inf_{(Λ_x)_x} Σ_{i<j} F(Λ(ρ_i), Λ(ρ_j)), where Λ(ρ_i) := Σ_x Tr[Λ_x ρ_i]|x⟩⟨x| is the measurement channel induced by applying the POVM (Λ_x)_x on the state ρ_i.\" The infimum is one real infimum over the dependent sum of all sizes m and all POVMs on Fin m. IsPOVM requires positivity of every effect and sum equal to the identity. It is not a nested infimum with an empty inner index type.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The affirmative existential statement", new Formula.Logic(Local("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                Question + " The answer quantifies natural dimensions d, tuple sizes r, and all tuples rho of DensityState (Fin d). Strict comparison is FU rho < FM rho.", AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("nmlw-measured-fidelity-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Three qubit states give a strict gap"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take d = 2 and r = 3 with the matrices I/2, diag(3/4,1/4), and the matrix with diagonal entries 1/2 and off-diagonal entries 1/4. For an effect E, its trace half a and its Z and X Bloch half-coordinates b,c satisfy a ≥ 0 and b²+c² ≤ a². An affine lower bound on the real unit disc gives a sum of the three classical pair costs at least (72/25)a + (53/100)(b+c). Summing over any finite POVM cancels the Bloch coordinates and yields FM ≥ 24/25. The two by two trace-norm identity gives FU < 24/25, proving strict separation. The estimate allows arbitrary finite POVMs and does not assert the exact value of FM."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nuradha-mishra-leditzky-wilde-measured-fidelity-gap"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("nmlw-measured-fidelity-" + (name == "FU" ? "fu" : name == "FM" ? "fm" : name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names) { if (items.Count > 0) items.Add(Dot); items.Add(X(name)); }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Q("D5", "S3", "Quantum", "Information", "NMLWMeasuredFidelitySeparation", name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula Parenthesized(Formula f) => Seq(F.Open, f, F.Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula NatType() => Seq(Mathbb, Grp(X("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(X("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinType(Formula n) => App(Q("Fin"), n);
    private static Formula MatrixType(Formula n) => App(Q("Matrix"), n, n, ComplexType());
    private static Formula DensityType(Formula d) => App(Q("D5", "S3", "Quantum", "Foundation", "FiniteStateChannel", "DensityState"), FinType(d));
    private static Formula TupleType() => new Formula.TypeArrow(FinType(X("r")), DensityType(X("d")));
    private static Formula LambdaFormula(string name, Formula type, Formula body) => Seq(Q("fun"), X(name), Colon, type, Mapsto, Sp, body);
    private static Formula StateMatrix(Formula i) => App(Q("CStarMatrix", "ofMatrix", "symm"), Call("val", App(X("rho"), i)));
    private static Formula Normalization() => new Formula.Fraction(D(2), Mul(Parenthesized(Seq(X("r"), Colon, RealType())), Parenthesized(new Formula.Binary(Parenthesized(Seq(X("r"), Colon, RealType())), FormulaBinaryOperator.Subtract, D(1)))));
    private static Formula Pairs(Formula body) => Seq(new Formula.Subscript(Sum, Seq(X("i"), Colon, FinType(X("r")))), new Formula.Subscript(Sum, Seq(X("j"), InMacro, Sp, App(Q("Finset", "Ioi"), X("i")))), Parenthesized(body));
    private static Formula PovmType() => Seq(new Formula.Subscript(Sigma, Seq(X("m"), Colon, NatType())),
        F.OpenBrace, X("L"), Colon, new Formula.TypeArrow(FinType(X("m")), MatrixType(FinType(X("d")))), Mid, Sp,
        App(Q("D5", "S3", "Quantum", "QuantumChannels", "ConcealmentKernelNecessityRefutation", "IsPOVM"), X("L")), F.CloseBrace);
    private static Formula AverageFormula(bool measured)
    {
        Formula Pair(Formula i, Formula j)
        {
            Formula State(Formula k) => measured
                ? App(Q("Matrix", "diagonal"), Parenthesized(LambdaFormula("x", FinType(Seq(X("P"), Dot, D(1))),
                    App(Q("Matrix", "trace"), Mul(App(Seq(X("P"), Dot, D(2), Dot, Q("val")), X("x")), StateMatrix(k))))))
                : StateMatrix(k);
            return App(Local("uhlmann"), State(i), State(j));
        }
        var sum = Pairs(Pair(X("i"), X("j")));
        Formula cost = measured ? Seq(new Formula.Subscript(Q("iInf"), Seq(X("P"), Colon, Parenthesized(PovmType()))), Parenthesized(sum)) : sum;
        return All("d", NatType(), All("r", NatType(), All("rho", TupleType(), Eq(App(Local(measured ? "FM" : "FU"), X("rho")), Mul(Normalization(), Parenthesized(cost))))));
    }
    private static Formula UhlmannFormula()
    {
        var product = Mul(App(Q("CFC", "sqrt"), X("rho")), App(Q("CFC", "sqrt"), X("sigma")));
        var body = Eq(App(Local("uhlmann"), X("rho"), X("sigma")),
            App(Q("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"), product));
        return All("n", Q("Type"), Seq(OpenBracket, App(Q("Fintype"), X("n")), CloseBracket,
            OpenBracket, App(Q("DecidableEq"), X("n")), CloseBracket,
            All("rho", MatrixType(X("n")), All("sigma", MatrixType(X("n")), body))));
    }
    private static Formula ClaimBody() => Ex("d", NatType(), Ex("r", NatType(), Ex("rho", TupleType(),
        new Formula.Relation(App(Local("FU"), X("rho")), FormulaRelationOperator.LessThan, App(Local("FM"), X("rho"))))));
}
