using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class FinitePathDisplacementsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/FinitePathDisplacements.";
    private static readonly LibraryNoteRef Bks =
        LibraryNoteRef.Create("D5/L/Words/bugeaudkriegershallit2009morphic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite roots and normalized periodic boundary corrections place every actual maximal-block length in finitely many affine power families.",
        H("Finite Paths and Coefficient Families"),
        Blocks(
            Paragraph(Text(
                "This owner closes the gap between eventual behavior along an infinite state trajectory and a "
                    + "uniform statement about every finite actual descent path. It carries the finite roots and "
                    + "literal edge contexts together with a common factorial period, then solves the length "
                    + "recurrence without claiming that every resulting coefficient family is attained.")),
            Node("exists_bounded_root_and_finite_path_displacements",
                "A factorial period works on every sufficiently deep finite path", FinitePathFormula(),
                "Choose the same support-stabilizing q and Q=P^q returned by the actual descent theorem. The "
                    + "owner retains Q-uniformity, the fixed-word equation, support stability, finite early roots, "
                    + "finite late root words, finite context pairs, and an actual root chain for every block. "
                    + "Let S be the cardinality of Alphabet x Alphabet and T=S!. Then T>0. For any finite block "
                    + "sequence whose first n+1 edges are actual descent steps, every j with S<=j and j+T<n has "
                    + "the same left and right signed displacement at edges j+1 and j+T+1. Pigeonhole gives a "
                    + "state period at most S, and divisibility by S! makes T a common period; no infinite chain "
                    + "is appended to the supplied finite path.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Bks)),
            Node("exists_finite_actual_maximal_block_coefficient_families",
                "Every actual block length belongs to one finite coefficient family", CoefficientFormula(),
                "For every finite letter set Delta, one finite set C of triples (a,b,c) is chosen before first and "
                    + "last. Every triple has c>0. For every actual maximal Delta interval [first,last], some triple "
                    + "in C and m in N satisfy c*(last+1-first)=a*P^m+b in the integers. The construction sets "
                    + "Q=P^q, T=(card(Alphabet x Alphabet))!, and A=Q^T. Short path lengths form a finite set. "
                    + "Longer paths split after a bounded prefix into T-step chunks; periodic signed corrections "
                    + "turn the length recurrence into an affine geometric progression with denominator A-1. "
                    + "Constant families cover bounded paths. Membership asserts containment only, not converse "
                    + "realization of every triple or exponent.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Bks)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("raney-finite-path-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula And(params Formula[] xs) => Join(xs, Land);
    private static Formula Implies(Formula a, Formula b) => Seq(Paren(a), Sp, Rightarrow, Sp, Paren(b));
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula Join(Formula[] xs, Formula op)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = Seq(result, Sp, op, Sp, xs[i]);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula LeftCorrection(Formula k) => Sub(
        Call("first", Call("blocks", Add(k, D(2)))),
        Mul(V("Q"), Call("first", Call("blocks", Add(k, D(1))))));
    private static Formula RightCorrection(Formula k) => Sub(
        Add(Call("last", Call("blocks", Add(k, D(2)))), D(1)),
        Mul(V("Q"), Add(Call("last", Call("blocks", Add(k, D(1)))), D(1))));

    private static Formula FinitePathFormula() => Disp(Ex("q", N(), And(
        LtF(D(0), V("q")),
        Call("finiteRootAndContextData", Pow(V("P"), V("q"))),
        Eqn(V("S"), Call("card", Call("Prod", V("Alphabet"), V("Alphabet")))),
        Eqn(V("T"), Call("factorial", V("S"))),
        LtF(D(0), V("T")),
        All("j", N(), Implies(And(LeF(V("S"), V("j")), LtF(Add(V("j"), V("T")), V("n")),
                Call("finiteActualDescentPath", V("Q"), V("blocks"), V("n"))),
            And(Eqn(LeftCorrection(Add(V("j"), V("T"))), LeftCorrection(V("j"))),
                Eqn(RightCorrection(Add(V("j"), V("T"))), RightCorrection(V("j")))))))));

    private static Formula CoefficientFormula()
    {
        var equation = Eqn(
            Mul(Call("third", V("abc")), Sub(Add(V("last"), D(1)), V("first"))),
            Add(Mul(Call("first", V("abc")), Pow(V("P"), V("m"))),
                Call("second", V("abc"))));
        var covered = All("first", N(), All("last", N(), Implies(
            Call("IsMaximalDeltaInterval", V("Delta"), V("w"), V("first"), V("last")),
            Ex("abc", Call("members", V("C")), Ex("m", N(), equation)))));
        var coefficients = Ex("C", Call("Finset", Call("Prod", Z(), Z(), N())), And(
            Paren(All("abc", Call("members", V("C")), LtF(D(0), Call("third", V("abc"))))),
            Paren(covered)));
        return Disp(All("Delta", Call("Finset", V("Alphabet")), coefficients));
    }
}
