using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FannesRootFidelityHolevoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/fannes2011fidelity");
    private const string Quotation = "Page 10, Conjecture 1: For any ensemble E₃ = {(pᵢ, ϱᵢ)} with K = 3 three states of arbitrary dimension d the corresponding Holevo quantity χ(E₃) is bounded from above by the entropy of the matrix C√F(E₃) defined in (16): χ(E₃) ≤ S(C√F(E₃)).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root-fidelity matrix entropy bounds the Holevo quantity of every three-state ensemble.",
        H("The three-state root-fidelity Holevo bound"),
        Blocks(
            Node("holevo", "Holevo quantity", HolevoFormula(),
                "Equation (2), page 3: χ(Eₖ) = S(ϱ) − ∑ᵢ pᵢ S(ϱᵢ), where ϱ = ∑ᵢ pᵢϱᵢ. Here the ensemble index is Fin 3.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rootFidelityMatrix", "Root-fidelity matrix", MatrixFormula(),
                "Equation (16), page 10: C√F(E₃) = [√(pᵢpⱼ)√Fᵢⱼ]ᵢⱼ. Each real matrix entry is embedded in the complex numbers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", Disp(new Formula.Logic(X("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))),
                Quotation + " A state is a positive semidefinite Matrix (Fin d) (Fin d) ℂ of trace one. The weights are nonnegative and sum to one. Every natural dimension is quantified; dimension zero has no such density matrix.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The Holevo bound for three arbitrary states", Disp(ClaimBody()),
                "Two polar gauges make two cross products positive. An eigenbasis of the remaining polar unitary preserves all three root fidelities in one rank-one decomposition. Channel data processing bounds the Holevo quantity by its labelled rank-one refinement. The three-by-three entrywise-modulus entropy inequality and diagonal entropy accounting then bound that refinement by the entropy of the root-fidelity matrix. Singular states and zero weights require no limiting restriction.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("fmrz-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(F.Open, x, F.Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula n) => Call("Matrix", n, n, C);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula SumOver(string i, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(X(i), Colon, type), Sp, Parenthesized(body));
    private static Formula Re(Formula a) => App(Q("Complex", "re"), a);
    private static Formula Trace(Formula a) => App(Q("Matrix", "trace"), a);
    private static Formula Psd(Formula a) => App(Q("Matrix", "PosSemidef"), a);
    private static Formula Log(Formula a) => App(Q("CFC", "log"), a);
    private static Formula TraceEntropy(Formula a) => Negate(Re(Trace(Mul(Parenthesized(a), Log(a)))));
    private static Formula Finite(string n, Formula body) => All(n, Q("Type"),
        Seq(OpenBracket, Call("Fintype", X(n)), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", X(n)), CloseBracket, Sp, body));

    private static Formula Ent(Formula a) => TraceEntropy(a);
    private static Formula Root(Formula a) => App(Q("CFC", "sqrt"), a);
    private static Formula Three => Fin(D(3));
    private static Formula Ensemble(Formula n, Formula body) => All("p", Arrow(Three, R), All("rho", Arrow(Three, Mat(n)), body));
    private static Formula Fidelity(Formula a, Formula b) =>
        App(Q("FiniteTraceDistance", "traceNorm"), Mul(Root(a), Root(b)));
    private static Formula Mixture() => SumOver("i", Three, Seq(Cast(App(X("p"), X("i")), C), Sp, Cdot, Sp, App(X("rho"), X("i"))));
    private static Formula HolevoFormula() => Disp(Finite("n", Ensemble(X("n"), Eq(Call("holevo", X("p"), X("rho")),
        Sub(Ent(Mixture()), SumOver("i", Three, Mul(App(X("p"), X("i")), Ent(App(X("rho"), X("i"))))))))));
    private static Formula MatrixEntry() => Cast(Cast(Mul(App(Q("Real", "sqrt"), Mul(App(X("p"), X("i")), App(X("p"), X("j")))),
        Fidelity(App(X("rho"), X("i")), App(X("rho"), X("j")))), R), C);
    private static Formula MatrixFormula() => Disp(Finite("n", Ensemble(X("n"),
        All("i", Three, All("j", Three, Eq(App(Call("rootFidelityMatrix", X("p"), X("rho")), X("i"), X("j")), MatrixEntry()))))));
    private static Formula ClaimBody()
    {
        var d = X("d");
        var states = All("i", Three, And(Psd(App(X("rho"), X("i"))), Eq(Trace(App(X("rho"), X("i"))), D(1))));
        var weights = All("i", Three, Le(D(0), App(X("p"), X("i"))));
        var total = Eq(SumOver("i", Three, App(X("p"), X("i"))), D(1));
        return All("d", N, All("rho", Arrow(Three, Mat(Fin(d))), All("p", Arrow(Three, R),
            Imp(states, Imp(weights, Imp(total, Le(Call("holevo", X("p"), X("rho")), Ent(Call("rootFidelityMatrix", X("p"), X("rho"))))))))));
    }
}
