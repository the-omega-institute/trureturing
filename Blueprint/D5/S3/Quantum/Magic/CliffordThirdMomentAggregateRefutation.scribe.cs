using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class CliffordThirdMomentAggregateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/zhu2024thirdmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The isotropic aggregate in Zhu, Mao and Yi's Conjecture 2 sums the third-moment expectations over stochastic orthogonal graph subspaces. A normalized two-qudit state in prime dimension five has aggregate 140241723/24017978, strictly below six.",
        H("An isotropic aggregate below six"),
        Blocks(
            Node("graph", "The oriented graph subspace", GraphFormula(),
                "For a three by three matrix O over ZMod d, the graph consists of pairs (Oy,y). The first component is the output and the second component is the input, as in the source operator r(T).",
                "graphSubspace", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graphinjective", "Graph subspaces determine their matrices", GraphInjectiveFormula(),
                "Equality of the oriented graphs forces equality of the output for every input. Applying this to the three coordinate vectors recovers every matrix column, so graphSubspace is injective.",
                "graphSubspace_injective", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("group", "Stochastic orthogonal matrices", GroupFormula(),
                "The source stochastic orthogonal group consists of matrices preserving x dot x for every vector x and fixing the all-ones vector.",
                "stochasticOrthogonal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polarization", "Polarization in dimension five", PolarizationFormula(),
                "Over ZMod 5, two is invertible. Expanding the preserved quadratic expression at x+y and subtracting the expressions at x and y proves preservation of x dot y. On coordinate vectors this is transpose(O) O = I. Conversely, that matrix identity preserves x dot x. The all-ones condition is the same on both sides.",
                "stochasticOrthogonal_five_iff", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("isosubspaces", "The collection of isotropic graph subspaces", IsoSubspacesFormula(),
                "The source collection is the image of the stochastic orthogonal group under graphSubspace. Injectivity ensures that summing over this collection counts each matrix graph exactly once.",
                "isoSubspaces", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("aggregate", "The aggregate isotropic expectation", AggregateFormula(),
                "The collection of isotropic subspaces is the set of graphs of stochastic orthogonal matrices. Its aggregate is the sum of kappa over exactly those graphs. The expectation kappa, the tensor operator R and the density tensor stateCube use the source trace convention.",
                "kappaIso", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("amplitudes", "Integer amplitudes", AmplitudesFormula(),
                "The integer amplitudes are indexed by the canonical representatives of the two coordinates in ZMod 5.",
                "v", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("state", "The normalized two-qudit state", StateFormula(),
                "Divide the integer amplitudes by the complex image of the positive real square root of 458.",
                "psi", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("normalization", "Unit squared norm", NormalizationFormula(),
                "The sum of the squared integer amplitudes is 458, so the scaled state has unit squared norm.",
                "normalized_psi", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("isovalue", "The exact isotropic aggregate", IsoValueFormula(),
                "The aggregate of this state over the isotropic graph subspaces is 140241723/24017978.",
                "kappa_iso", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("identityvalue", "The identity graph expectation", IdentityValueFormula(),
                "For every normalized state, the identity graph has third-moment expectation one.",
                "kappa_identity", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("rowvalue", "Row permutation invariance", RowValueFormula(),
                "Permuting the three output rows leaves the product of three state amplitudes unchanged, and therefore preserves the graph expectation.",
                "kappa_rows", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("claim", "The aggregate lower bound in Conjecture 2", ClaimFormula(),
                "The assertion quantifies over every prime dimension other than two, every number of qudits and every normalized complex state. The complex order requires that the aggregate have zero imaginary part and real part at least six.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A two-qudit state refutes the bound", new Formula.Not(F.Id("claim")),
                "Take d = 5 and n = 2. The row labels the first qudit and the column labels the second. The integer amplitude matrix has rows (8,-5,0,4,5), (0,3,6,4,-4), (-2,-5,-3,0,3), (-3,0,5,-8,-6), (5,-4,2,-5,0). Divide each amplitude by sqrt(458); the sum of squared amplitudes is 458. The stochastic orthogonal group has twelve matrices: the six permutation matrices and the six row permutations of the matrix with rows (3,4,4), (4,3,4), (4,4,3). For a graph, the trace collapses to a sum over three input copies, with O acting separately on each qudit column. Permuting the rows leaves this expectation unchanged. Each permutation matrix gives one, while each of the other six matrices gives -2577430/(458^3). The latter numerator is the exact integer sum of 15625 products of six amplitudes. Thus the aggregate is 140241723/24017978, and six times the denominator exceeds the numerator by 3866145.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-2024-clifford-third-moment-aggregate-lower-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("clifford-aggregate-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Of(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Field(Formula d) => Call("ZMod", d);
    private static Formula Config(Formula d, Formula n) => Arrow(Fin(n), Field(d));
    private static Formula Vectors(Formula d, Formula n) => Arrow(Config(d, n), Complex());
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Square(Formula a) => new Formula.Power(a, D(2));
    private static Formula Sum(Formula x, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula Mat(Formula d) => Call("Matrix", Fin(D(3)), Fin(D(3)), Field(d));
    private static Formula Instance(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket, Sp);
    private static Formula One() => Lambda(Underscore, Fin(D(3)), D(1));
    private static Formula Transpose(Formula o) => Call("transpose", o);
    private static Formula Subspaces(Formula d) => Call("Submodule", Field(d),
        Parenthesized(Seq(Parenthesized(Config(d, D(3))), Sp, Times, Sp,
            Parenthesized(Config(d, D(3))))));
    private static Formula SourceCondition(Formula d, Formula o)
    {
        Formula x = F.Id("x"), ox = Call("mulVec", o, x);
        return And(All(x, Config(d, D(3)),
            Eq(Call("dotProduct", ox, ox), Call("dotProduct", x, x))),
            Eq(Call("mulVec", o, One()), One()));
    }

    private static Formula GraphFormula()
    {
        Formula d = F.Id("d"), o = F.Id("O"), y = F.Id("y");
        return All(d, Nat(), All(o, Mat(d),
            Eq(Call("graphSubspace", o), Call("range", Lambda(y, Config(d, D(3)),
                Pair(Call("mulVec", o, y), y))))));
    }

    private static Formula GroupFormula()
    {
        Formula d = F.Id("d"), o = F.Id("O");
        return All(d, Nat(), Seq(Instance("NeZero", d),
            Eq(Call("stochasticOrthogonal", d),
                Call("filter", Lambda(o, Mat(d), SourceCondition(d, o)), Call("univ", Mat(d))))));
    }

    private static Formula GraphInjectiveFormula()
    {
        Formula d = F.Id("d");
        Formula graph = Of(Named("graphSubspace"),
            Parenthesized(Seq(F.Id("d"), Sp, Colon, F.Eq, Sp, d)));
        return All(d, Nat(), Call("Injective", graph));
    }

    private static Formula PolarizationFormula()
    {
        Formula d = D(5), o = F.Id("O");
        Formula condition = And(Eq(Mul(Transpose(o), o), D(1)),
            Eq(Call("mulVec", o, One()), One()));
        return All(o, Mat(d), Iff(SourceCondition(d, o), condition));
    }

    private static Formula IsoSubspacesFormula()
    {
        Formula d = F.Id("d");
        return All(d, Nat(), Seq(Instance("NeZero", d),
            Eq(Call("isoSubspaces", d),
                Call("image", Named("graphSubspace"), Call("stochasticOrthogonal", d)))));
    }

    private static Formula AggregateFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), t = F.Id("T");
        Formula domain = Seq(t, Sp, Colon, Sp, Subspaces(d), Comma, Sp,
            t, Sp, InMacro, Sp, Call("isoSubspaces", d));
        Formula sum = Seq(F.Sum, Underscore, Grp(domain), Sp,
            Parenthesized(Call("kappa", d, n, psi, t)));
        return All(d, Nat(), All(n, Nat(), Seq(Instance("NeZero", d),
            All(psi, Vectors(d, n), Eq(Call("kappaIso", d, n, psi), sum)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), x = F.Id("x");
        Formula normalized = Eq(Sum(x, Config(d, n), Square(new Formula.Norm(Of(psi, x)))), D(1));
        return Iff(F.Id("claim"), All(d, Nat(), Seq(
            Instance("Fact", Call("Prime", d)), Imp(Ne(d, D(2)),
                All(n, Nat(), All(psi, Vectors(d, n), Imp(normalized,
                    Le(Parenthesized(Seq(D(6), Sp, Colon, Sp, Complex())), Call("kappaIso", d, n, psi)))))))));
    }
    private static Formula Signed(int n) => n < 0 ? Seq(Minus, Number(-n)) : Number(n);
    private static Formula Number(int n) => D([.. n.ToString(System.Globalization.CultureInfo.InvariantCulture)
        .Select(c => (byte)(c - '0'))]);
    private static Formula AmplitudeMatrix()
    {
        int[][] rows = [[8,-5,0,4,5], [0,3,6,4,-4], [-2,-5,-3,0,3],
            [-3,0,5,-8,-6], [5,-4,2,-5,0]];
        var entries = new List<Formula> { Bang, Bang, OpenBracket };
        for (int i = 0; i < rows.Length; i++)
        {
            if (i > 0) entries.Add(Semi);
            for (int j = 0; j < rows[i].Length; j++)
            {
                if (j > 0) entries.Add(Comma);
                entries.Add(Signed(rows[i][j]));
            }
        }
        entries.Add(CloseBracket);
        return Seq([.. entries]);
    }
    private static Formula FinIndex(Formula a) => Seq(Langle, Sp, Call("val", a), Comma, Sp,
        Of(Seq(Operatorname, Grp(F.Id("ZMod"), Dot, F.Id("val"), Underscore, Grp(F.Id("lt")))), a),
        Sp, Rangle);
    private static Formula AmplitudesFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return All(a, Field(D(5)), All(b, Field(D(5)),
            Eq(Call("v", a, b), Of(AmplitudeMatrix(), FinIndex(a), FinIndex(b)))));
    }
    private static Formula StateFormula()
    {
        Formula x = F.Id("x");
        Formula numerator = Parenthesized(Seq(Call("v", Of(x, D(0)), Of(x, D(1))),
            Sp, Colon, Sp, Complex()));
        Formula denominator = Parenthesized(Seq(Call("sqrt", Number(458)), Sp, Colon, Sp, Complex()));
        return All(x, Config(D(5), D(2)), Eq(Call("psi", x), new Formula.Fraction(numerator, denominator)));
    }
    private static Formula Normalized(Formula d, Formula n, Formula psi)
    {
        Formula x = F.Id("x");
        return Eq(Sum(x, Config(d, n), Square(new Formula.Norm(Of(psi, x)))), D(1));
    }
    private static Formula NormalizationFormula() => Normalized(D(5), D(2), F.Id("psi"));
    private static Formula IsoValueFormula() => Eq(Call("kappaIso", D(5), D(2), F.Id("psi")),
        new Formula.Fraction(Number(140241723), Number(24017978)));
    private static Formula IdentityValueFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi");
        return All(d, Nat(), All(n, Nat(), Seq(Instance("NeZero", d),
            All(psi, Vectors(d, n), Imp(Seq(F.Id("hn"), Sp, Colon, Sp, Normalized(d, n, psi)),
                Eq(Call("kappa", d, n, psi, Call("graphSubspace", D(1))), D(1)))))));
    }
    private static Formula RowValueFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), o = F.Id("O"), psi = F.Id("Psi"), e = F.Id("e");
        return All(d, Nat(), All(n, Nat(), Seq(Instance("NeZero", d),
            All(o, Mat(d), All(psi, Vectors(d, n), All(e, Call("Perm", Fin(D(3))),
                Eq(Call("kappa", d, n, psi, Call("graphSubspace", Call("submatrix", o, e, Named("id")))),
                    Call("kappa", d, n, psi, Call("graphSubspace", o)))))))));
    }

}
