using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class MultivariateQSPCollapseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/laneve2024multivariateqsp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-step three-level quantum signal protocol returns from effective dimension three to two without a common monomial action on any subspace of dimension at least two.",
        H("A counterexample to Laneve--Wolf Conjecture 8"),
        Blocks(
            Node("polynomial-state", "Polynomial states on the torus", PolyStateFormula(),
                "A polynomial state is a vector of three complex polynomials in two variables. Its squared Euclidean norm is one whenever both variables have modulus one. The variables a and b are X(0) and X(1).",
                "PolyState", DescribeRole.Definition),
            Node("effective-dimension", "Effective dimension", EffDimFormula(),
                "For each exponent s, collect the coefficient of that monomial in each of the three coordinates. The effective dimension is the complex dimension of the span of all these coefficient vectors.",
                "effDim", DescribeRole.Definition),
            Node("signal-step", "The three-level signal", SignalFormula(),
                "The signal leaves the first coordinate unchanged and multiplies the second and third by a and b, respectively. This is the polynomial action of diag(1,a,b).",
                "signalStep", DescribeRole.Definition),
            Node("stages", "Protocol C stages", StageFormula(),
                "Stage zero is the input. For j less than m, stage j+1 applies the signal to stage j and then applies the constant special unitary processing matrix A(j). Thus the array index j denotes the paper's A_(j+1). Stages after m equal stage m. The constant-polynomial embedding is C, and val extracts the matrix from its special-unitary subtype.",
                "stage", DescribeRole.Definition),
            Node("transfer", "The evaluated transfer operator", TransferFormula(),
                "The prefix transfer starts at the identity. For j less than m its next value is A(j) diag(1,a,b) times its current value, and after m it stays constant. The transfer is the prefix at m, namely A_m diag(1,a,b) ... A_1 diag(1,a,b).",
                "transfer", DescribeRole.Definition),
            Node("claim", "The subspace-isometry conclusion", ClaimFormula(),
                "Conjecture 8 asserts this conclusion for polynomial states whose input and output have effective dimension at most two while every strictly intermediate state has effective dimension greater than two. The conclusion permits any pair of complex subspaces and any linear isometric equivalence between them, with arbitrary natural exponents. In particular, no coordinate subspace, chosen basis, or predetermined monomial is required.",
                "claim", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("multivariate-qsp-collapse-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation"), StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take m=2 with A_1 the cycle sending (x,y,z) to (z,x,y) and A_2 the inverse cycle. Both matrices are special unitary. The initial state is (3,4,12a)/13; its norm is one on the torus since 9+16+144=169. The next two states are (12ab,3,4a)/13 and (3a,4ab,12ab)/13. Their coefficient spans have dimensions two, three, and two, respectively.")),
                    Paragraph(Text(
                        "The transfer is diag(a,ab,b). If it equals a^k b^h U on a subspace H, evaluation at (1,1) forces Ux=x in the ambient three-dimensional space. Evaluation at (i,-1) then forces diag(i,-i,-1)x=i^k(-1)^h x for every x in H. The three diagonal entries are distinct, so projection onto the coordinate with that scalar eigenvalue is injective on H. Consequently H has dimension at most one, contradicting the required dimension of at least two. The collision of the last two output monomials therefore does not imply a common monomial action on a fixed two-dimensional subspace."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("laneve-2024-qsp-collapse-conjecture-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("multivariate-qsp-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Both(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fun(string name, Formula type, Formula body) => Seq(Open, F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula Polynomials() => Call("MvPolynomial", Fin(2), Complexes());
    private static Formula Vectors() => Arrow(Fin(3), Complexes());
    private static Formula PolyVectors() => Arrow(Fin(3), Polynomials());
    private static Formula Subspaces() => Call("Submodule", Complexes(), Vectors());
    private static Formula Processing() => Arrow(Call("Fin", F.Id("m")), Call("specialUnitaryGroup", Fin(3), Complexes()));
    private static Formula Tuple(params Formula[] entries)
    {
        var parts = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (int index = 0; index < entries.Length; index++)
        {
            if (index > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(entries[index]);
        }
        parts.Add(CloseBracket);
        return Seq([.. parts]);
    }
    private static Formula SumFin(string name, byte size, Formula body) => Seq(Sum, Underscore, Grp(F.Id(name), Colon, Sp, Fin(size)), Sp, body);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Smul(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Rank(Formula space) => Call("finrank", Complexes(), space);
    private static Formula Stage(Formula g, Formula j) => Call("stage", F.Id("A"), g, j);
    private static Formula UnitNorm(Formula value) => Eqn(new Formula.Norm(value), D(1));

    private static Formula PolyStateFormula()
    {
        Formula g = F.Id("g"), a = F.Id("a"), b = F.Id("b"), i = F.Id("i");
        Formula normalization = All("a", Complexes(), All("b", Complexes(),
            Imp(UnitNorm(a), Imp(UnitNorm(b), Eqn(SumFin("i", 3,
                new Formula.Power(new Formula.Norm(Call("eval", Tuple(a, b), App(g, i))), D(2))), D(1))))));
        return Disp(Eqn(F.Id("PolyState"), Seq(OpenBrace, Sp, g, Colon, Sp, PolyVectors(),
            Sp, Mid, Sp, normalization, Sp, CloseBrace)));
    }

    private static Formula EffDimFormula()
    {
        Formula coefficients = Fun("s", Call("Finsupp", Fin(2), Naturals()),
            Fun("i", Fin(3), Call("coeff", App(F.Id("g"), F.Id("i")), F.Id("s"))));
        return Disp(All("g", PolyVectors(), Eqn(Call("effDim", F.Id("g")),
            Rank(Call("span", Complexes(), Call("range", coefficients))))));
    }

    private static Formula SignalFormula()
    {
        Formula g = F.Id("g");
        return Disp(All("g", PolyVectors(), Eqn(Call("signalStep", g), Tuple(
            App(g, D(0)), Mul(Call("X", D(0)), App(g, D(1))),
            Mul(Call("X", D(1)), App(g, D(2)))))));
    }

    private static Formula StageFormula()
    {
        Formula g = F.Id("g"), j = F.Id("j"), i = F.Id("i"), l = F.Id("l");
        Formula next = Add(j, D(1));
        Formula matrixEntry = App(Val(App(F.Id("A"), Call("Finmk", j, F.Id("hj")))), i, l);
        Formula valid = All("hj", LtTo(j, F.Id("m")), All("i", Fin(3),
            Eqn(App(Stage(g, next), i), SumFin("l", 3,
                Mul(Call("C", matrixEntry), App(Call("signalStep", Stage(g, j)), l))))));
        Formula stopped = Imp(Seq(Neg, Sp, Par(LtTo(j, F.Id("m")))), Eqn(Stage(g, next), Stage(g, j)));
        return Disp(All("m", Naturals(), All("A", Processing(), All("g", PolyVectors(),
            Both(Eqn(Stage(g, D(0)), g), All("j", Naturals(), Both(valid, stopped)))))));
    }

    private static Formula TransferFormula() => Disp(All("m", Naturals(), All("A", Processing(),
        All("a", Complexes(), All("b", Complexes(), Eqn(
            Call("transfer", F.Id("A"), F.Id("a"), F.Id("b")),
            Call("transferPrefix", F.Id("A"), F.Id("a"), F.Id("b"), F.Id("m"))))))));

    private static Formula ClaimFormula()
    {
        Formula g = F.Id("g"), m = F.Id("m"), j = F.Id("j");
        Formula a = F.Id("a"), b = F.Id("b"), x = F.Id("x");
        Formula action = All("a", Complexes(), All("b", Complexes(), Imp(UnitNorm(a), Imp(UnitNorm(b),
            All("x", F.Id("H"), Eqn(Call("mulVec", Call("transfer", F.Id("A"), a, b), Val(x)),
                Smul(Mul(new Formula.Power(a, F.Id("k")), new Formula.Power(b, F.Id("h"))),
                    Val(App(F.Id("U"), x)))))))));
        Formula conclusion = Some("H", Subspaces(), Some("Hprime", Subspaces(),
            Some("U", Call("LinearIsometryEquiv", Call("RingHomId", Complexes()), F.Id("H"), F.Id("Hprime")),
                Some("k", Naturals(), Some("h", Naturals(), Both(LeqTo(D(2), Rank(F.Id("H"))), action))))));
        Formula intermediate = All("j", Naturals(), Imp(LtTo(D(0), j), Imp(LtTo(j, m),
            LtTo(D(2), Call("effDim", Stage(Val(g), j))))));
        Formula statement = All("m", Naturals(), All("A", Processing(), All("g", F.Id("PolyState"),
            Imp(LeqTo(Call("effDim", Val(g)), D(2)),
                Imp(LeqTo(Call("effDim", Stage(Val(g), m)), D(2)), Imp(intermediate, conclusion))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Par(statement)));
    }
}
