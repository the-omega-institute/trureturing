using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FourMUBBoundEntanglementRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/baebera2022mubbound");
    private const string Conjecture = "Conjecture 1. If d = 2^r and r > 1, the minimal number of MUBs required for bound entanglement detection equals m = d/2 + 1 = 2^{r−1} + 1.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four mutually unbiased bases in dimension eight give a negative expectation on a positive-partial-transpose density matrix for the witness of Bae, Bera, Chruściński, Hiesmayr and McNulty.",
        H("Four MUBs refute the dimension-eight necessity bound"),
        Blocks(
            Node("IsMUBFamily", "Mutually unbiased bases", MUBFormula(),
                "Section I, p. 2: 'Generalising to larger collections of measurements, we say a set of bases is mutually unbiased if all bases are pairwise unbiased.' Columns are basis vectors. Each basis matrix is unitary, basis zero is the identity whenever the family is nonempty, and the squared norm of every overlap between distinct bases is 1/d. The implicit natural-number parameters d and m are shown explicitly.", true),
            Node("witnessGamma", "The partially transposed MUB witness", WitnessFormula(),
                "Equation (4), p. 3: W(M_m, s) = ((d+m−1)/d) 𝟙 ⊗ 𝟙 − B(M_m, s). The formula displays its partial transpose: the computational term pairs l with l+s modulo d, and each nonzero basis index contributes equal-column tensor projectors with conjugation on the second factor. Matrix.vecMulVec forms each column projector. Fin addition is modulo d. The coefficient is complex scalar multiplication; val marks the natural-to-complex casts before subtraction and division.", true),
            Node("DetectsBoundEntanglement", "Detection of a PPT density matrix", DetectionFormula(),
                "A detected state is a density matrix whose partial transpose on the second subsystem is positive semidefinite and whose real witness expectation is strictly negative. IsDensity and partialTransposeB are the existing pair-indexed matrix operations in StructuredNegativityCoincidenceRefutation. The source's nonnegativity on separable states supplies the physical interpretation of a negative expectation.", true),
            Node("claim", "The necessity half of Conjecture 1", ClaimFormula(),
                "Section VIII, p. 8: '" + Conjecture + "' The preceding sentence reads: 'When d = 2^r, we predict that d/2 + 1 MUBs are both necessary and sufficient for the witness W^Γ(M_m, s) to be non-decomposable.' The formula states the necessity half for every natural r at least two, every family size below 2^(r−1)+1, every MUB family and every modular shift. Subtraction r−1 is natural subtraction. Refuting this half refutes the stated equality for the minimum.", true),
            Node("result", "Refutation in dimension eight", Disp(new Formula.Not(F.Id("claim"))),
                "Take r=3, m=4 and s=1. The bases are I, H/√8, diag(a)H/√8 and diag(b)H/√8, where H[x,k]=(−1)^(x·k) for the three binary coordinates, a=(1,1,i,i,i,−i,−1,1), and b=(1,1,1,−1,i,i,−i,i). Their overlap calculations use Walsh multiplication and finite character sums. The rational state is M/10134, with eight XOR sectors, each of the form [[A,B],[B,A]]. Thirty-two separate LDL identities with 128 positive pivots prove that the state and its partial transpose are positive semidefinite. Its trace is one and its exact witness expectation is −14/563. Thus four bases detect a PPT density matrix although the conjecture requires at least five. The proof establishes positive semidefiniteness, without a public strict-positivity or optimal-minimum statement.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolutionClaim = null) => Describe.Lean(
            DescribeId.Create("fourmub-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolutionClaim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp, x, Colon, type, Comma, Sp, body);
    private static Formula Ex(Formula x, Formula type, Formula body) => Seq(Exists, Sp, x, Colon, type, Comma, Sp, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(Call("val", x), Colon, type));
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Dim => F.Id("d");
    private static Formula Count => F.Id("m");
    private static Formula U => F.Id("U");
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula MatrixType(Formula index) => Call("Matrix", index, index, ComplexType);
    private static Formula BasesType(Formula d, Formula m) => Arrow(Fin(m), MatrixType(Fin(d)));
    private static Formula PairIndex => Seq(Fin(Dim), Sp, F.Times, Sp, Fin(Dim));
    private static Formula BipartiteType => MatrixType(PairIndex);
    private static Formula BindBases(Formula body) => All(Dim, NatType, All(Count, NatType, All(U, BasesType(Dim, Count), body)));
    private static Formula Lambda(Formula x, Formula type, Formula body) => Parenthesized(Seq(Named("fun"), Sp, x, Colon, type, Sp, Mapsto, Sp, body));
    private static Formula TypedSum(Formula x, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(x, Colon, type)), Sp, Parenthesized(body));
    private static Formula Projector(Formula alpha, Formula i)
    {
        Formula x = F.Id("x");
        var column = Lambda(x, Fin(Dim), App(U, alpha, x, i));
        return App(Qualified("Matrix", "vecMulVec"), column, Call("star", column));
    }

    private static Formula MUBFormula()
    {
        Formula alpha = F.Id("alpha"), beta = F.Id("beta"), i = F.Id("i"), j = F.Id("j"), hm = F.Id("hm");
        var unitary = All(alpha, Fin(Count), Seq(App(U, alpha), Sp, InMacro, Sp,
            App(Qualified("Matrix", "unitaryGroup"), Fin(Dim), ComplexType)));
        var canonical = All(hm, Rel(D(0), FormulaRelationOperator.LessThan, Count),
            Eq(App(U, App(Qualified("Fin", "mk"), D(0), hm)), D(1)));
        var overlap = App(new Formula.Binary(App(Qualified("Matrix", "conjTranspose"), App(U, alpha)),
            FormulaBinaryOperator.Multiply, App(U, beta)), i, j);
        var unbiased = All(alpha, Fin(Count), All(beta, Fin(Count), Imp(
            Seq(alpha, Sp, Neq, Sp, beta), All(i, Fin(Dim), All(j, Fin(Dim),
                Eq(Pow(Call("norm", overlap), D(2)), new Formula.Fraction(D(1), Cast(Dim, RealType))))))));
        return Disp(BindBases(Iff(Call("IsMUBFamily", U), And(unitary, And(canonical, unbiased)))));
    }

    private static Formula WitnessFormula()
    {
        Formula s = F.Id("s"), l = F.Id("l"), alpha = F.Id("alpha"), i = F.Id("i");
        var coefficient = new Formula.Fraction(Sub(Add(Cast(Dim, ComplexType), Cast(Count, ComplexType)), D(1)), Cast(Dim, ComplexType));
        var diagonal = TypedSum(l, Fin(Dim), App(Qualified("Matrix", "single"), Pair(l, Add(l, s)), Pair(l, Add(l, s)), Parenthesized(Seq(D(1), Colon, ComplexType))));
        var filter = App(Qualified("Finset", "filter"), Lambda(alpha, Fin(Count), Seq(Call("val", alpha), Sp, Neq, Sp, D(0))),
            Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Call("Finset", Fin(Count)))));
        var tensor = App(Qualified("Matrix", "kronecker"), Projector(alpha, i),
            App(Qualified("Matrix", "map"), Projector(alpha, i), Parenthesized(Seq(Named("star"), Colon, Arrow(ComplexType, ComplexType)))));
        var correlators = Seq(new Formula.Subscript(Sum, Seq(alpha, Sp, InMacro, Sp, filter)), Sp, TypedSum(i, Fin(Dim), tensor));
        var scaledIdentity = Seq(coefficient, Sp, F.Cdot, Sp, D(1));
        return Disp(BindBases(All(s, Fin(Dim), Eq(Call("witnessGamma", U, s), Sub(Sub(scaledIdentity, diagonal), correlators)))));
    }

    private static Formula DetectionFormula()
    {
        Formula s = F.Id("s"), rho = F.Id("rho");
        var product = new Formula.Binary(Call("witnessGamma", U, s), FormulaBinaryOperator.Multiply, rho);
        var trace = App(Qualified("Matrix", "trace"), product);
        var body = Ex(rho, BipartiteType, And(App(Qualified("StructuredNegativityCoincidenceRefutation", "IsDensity"), rho),
            And(App(Qualified("Matrix", "PosSemidef"), App(Qualified("StructuredNegativityCoincidenceRefutation", "partialTransposeB"), rho)),
                Rel(App(Qualified("Complex", "re"), trace), FormulaRelationOperator.LessThan, D(0)))));
        return Disp(BindBases(All(s, Fin(Dim), Iff(Call("DetectsBoundEntanglement", U, s), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s");
        var d = Pow(D(2), r);
        return Disp(Iff(F.Id("claim"), All(r, NatType, Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, r),
            All(Count, NatType, Imp(Rel(Count, FormulaRelationOperator.LessThan, Add(Pow(D(2), Parenthesized(Sub(r, D(1)))), D(1))),
                All(U, BasesType(d, Count), Imp(Call("IsMUBFamily", U),
                    All(s, Fin(d), new Formula.Not(Call("DetectsBoundEntanglement", U, s)))))))))));
    }
}
