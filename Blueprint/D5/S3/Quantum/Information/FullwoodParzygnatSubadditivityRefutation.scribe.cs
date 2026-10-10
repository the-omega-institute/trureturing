using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FullwoodParzygnatSubadditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/fullwood2025dynamical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Werner–Holevo channel on the maximally mixed five-level state gives a two-time pseudo-density matrix whose signed entropy exceeds the sum of its marginal entropies.",
        H("Subadditivity of quantum states over time"),
        Blocks(
            Node("jamio", "Input-first Jamiołkowski matrix", JamioFormula(),
                "The input factor precedes the output factor. The matrix unit inside the channel has its indices reversed: this is the Jamiołkowski convention of Fullwood and Parzygnat, rather than the Choi convention. The carrier is Fin n times Fin m, matching the factor order in rho tensor the output identity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pdm", "Two-time pseudo-density matrix", PdmFormula(),
                "Equation (15) defines a quantum state over time by half the anticommutator of rho tensor the output identity with the Jamiołkowski matrix. The channel is a complex-linear map between full matrix algebras.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S", "Signed spectral entropy", EntropyFormula(),
                "The real functional calculus applies the function x maps to -x log |x|. For Hermitian matrices, the spectral theorem identifies the real trace with the sum of this function over the eigenvalues, counted with multiplicity. This includes negative eigenvalues with their sign retained. Real.log |0| is zero, so the zero-eigenvalue contribution is zero. The total definition has no Hermiticity proof argument; the conjecture uses its Hermitian domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Fullwood–Parzygnat subadditivity conjecture", ClaimFormula(),
                "Remark 1 of On Dynamical Measures of Quantum Information conjectures subadditivity on quantum states over time. Both dimensions are positive. The input is positive semidefinite with trace one, and the arbitrary finite Kraus family satisfies the completeness equation. ofKraus(K,K) is FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus, whose action is the sum of K_k X K_k adjoint. Thus the hypothesis gives a completely positive trace-preserving map. The bound compares the signed entropy of the two-time matrix with the entropies of the input and output states. Fullwood and Yang, arXiv:2608.28946v1, Section 6, also state the higher-dimensional question as open.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A five-level Werner–Holevo counterexample", Disp(new Formula.Not(F.Id("claim"))),
                "Let rho be the identity divided by five and use the ten Kraus operators (E_ij - E_ji)/2, one for each i < j. Their adjoint products sum to the identity. Their channel action is (trace(X) I - transpose(X))/4 and fixes rho. Let Omega have entry one exactly on equal input and output indices, and let P be its outer product divided by five. P is a Hermitian idempotent of trace one. The Jamiołkowski matrix is (I - 5P)/4, and the two-time matrix is (I - 5P)/20. Its eigenvalues are -1/5 once and 1/20 twenty-four times. A two-point functional calculus on P gives entropy log 5 + (6/5) log 4. Each marginal entropy is log 5. The excess is (1/5) log(4096/3125), which is strictly positive because 4096 > 3125. This contradicts the universal subadditivity bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fullwood-parzygnat-2025-states-over-time-subadditivity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("fwp-subadditivity-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula rows, Formula cols) => Call("Matrix", rows, cols, Complexes);
    private static Formula Square(Formula n) => Mat(n, n);
    private static Formula Channel(Formula n, Formula m) => Call("LinearMap", Complexes, Square(FinOf(n)), Square(FinOf(m)));
    private static Formula SumOver(Formula x, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(x, Colon, type), Sp, Par(body));
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Par(Seq(x, Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);

    private static Formula JamioFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), e = F.Id("E"), i = F.Id("i"), j = F.Id("j");
        Formula sum = SumOver(i, FinOf(n), SumOver(j, FinOf(n),
            Call("kronecker", Call("single", i, j, D(1)), Apply(e, Call("single", j, i, D(1))))));
        return Disp(All("n", Naturals, All("m", Naturals, All("E", Channel(n, m), EqTo(Call("jamio", e), sum)))));
    }

    private static Formula PdmFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), rho = F.Id("rho"), e = F.Id("E");
        Formula r = Call("kronecker", rho, Par(Seq(D(1), Colon, Square(FinOf(m)))));
        Formula j = Call("jamio", e);
        return Disp(All("n", Naturals, All("m", Naturals, All("rho", Square(FinOf(n)),
            All("E", Channel(n, m), EqTo(Call("pdm", rho, e),
                Call("smul", Div(D(1), D(2)), Add(Mul(r, j), Mul(j, r)))))))));
    }

    private static Formula EntropyFormula()
    {
        Formula t = F.Id("t"), x = F.Id("X"), r = F.Id("r");
        Formula f = Lambda(r, Reals, Mul(new Formula.Negate(r), Call("log", Call("abs", r))));
        Formula body = All("X", Square(t), EqTo(Call("S", x), Call("realPart", Call("trace", Call("cfc", f, x)))));
        return Disp(All("t", Named("Type"), Instance("Fintype", t, Instance("DecidableEq", t, body))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), rho = F.Id("rho"), iota = F.Id("iota"),
            k = F.Id("K"), i = F.Id("k");
        Formula e = Call("ofKraus", k, k);
        Formula complete = EqTo(SumOver(i, iota, Mul(Call("conjTranspose", Apply(k, i)), Apply(k, i))), D(1));
        Formula bound = LeqTo(Call("S", Call("pdm", rho, e)), Add(Call("S", rho), Call("S", Apply(e, rho))));
        Formula families = All("iota", Named("Type"), Instance("Fintype", iota,
            All("K", new Formula.TypeArrow(iota, Mat(FinOf(m), FinOf(n))), Imp(complete, bound))));
        Formula inputs = All("rho", Square(FinOf(n)), Imp(Call("PosSemidef", rho),
            Imp(EqTo(Call("trace", rho), D(1)), families)));
        Formula body = All("n", Naturals, All("m", Naturals,
            Imp(LeqTo(D(1), n), Imp(LeqTo(D(1), m), inputs))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Par(body)));
    }
}
