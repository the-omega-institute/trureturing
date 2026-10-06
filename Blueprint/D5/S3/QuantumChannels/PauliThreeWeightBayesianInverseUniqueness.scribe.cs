using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class PauliThreeWeightBayesianInverseUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ting2026operational");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ting, Fullwood and Wu (arXiv:2605.10375) characterize when a unital qubit channel has a Bayesian inverse with respect to a state, and for Pauli channels with exactly three non-zero weights leave open whether the maximally mixed state is the only such state. It is: for every Pauli channel whose probability vector has exactly three non-zero entries, a completely positive trace-preserving Bayesian inverse with respect to a qubit state exists if and only if the state is the maximally mixed state.",
        H("Three-weight Pauli channels have Bayesian inverses only at the maximally mixed state"),
        Blocks(
            Node("paulis", "The Pauli matrices", PaulisFormula(),
                "sigma lists the identity and the Pauli matrices X, Y = i X Z and Z of the frozen pauliMatrix, indexed by Fin 4.",
                "sigma", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("channel", "The Pauli channel", ChannelFormula(),
                "The Pauli channel with probability vector p acts by A -> sum over mu of p_mu sigma_mu A sigma_mu, as a complex-linear map on 2 x 2 matrices.",
                "pauliChannel", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jamiolkowski", "The Jamiolkowski matrix", JamFormula(),
                "J[N] = (id tensor N)(SWAP) with SWAP = sum over i, j of |i><j| tensor |j><i|, written with the matrix units single(i, j, 1) and the Kronecker product.",
                "jam", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bayes", "Bayesian inverse", BayesFormula(),
                "F is a Bayesian inverse of E with respect to rho when F is completely positive and trace preserving and the quantum Bayes rule {E(rho) tensor 1, J[F]} = {1 tensor rho, J[E^dagger]} holds, written with the anticommutators expanded; Eadj is the channel standing for the Hilbert-Schmidt adjoint E^dagger.",
                "IsBayesianInverse", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Uniqueness of the maximally mixed state", ClaimFormula(),
                "For every probability vector p with exactly three non-zero entries: the Pauli channel equals its own Hilbert-Schmidt adjoint, which justifies using it in the place of E^dagger, and for every density matrix rho (pure states included) a Bayesian inverse with respect to rho exists if and only if rho is the maximally mixed state 1/2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Bayesian inverses of three-weight Pauli channels", Disp(F.Id("claim")),
                "At the maximally mixed state the channel itself is a Bayesian inverse: it is completely positive with Kraus operators sqrt(p_mu) sigma_mu, trace preserving, and both sides of the Bayes rule equal J of the channel because the channel fixes 1/2. Conversely, write rho = (1 + r . sigma)/2 with r != 0. The Bayes rule determines the image of 1 and of each sigma_j under any candidate inverse, so the candidate's Choi matrix is fixed by p and r. With h_i = (1 - p_i) r_i for the three active weights (the zero weight in any of the four positions is handled by relabelling the Pauli indices), the vector w = (1 tensor (1 - h . sigma)) applied to the unnormalized maximally entangled vector gives w* C w = -4[(1 - |h|^2) B + K A]/D with A, B, K >= 0, B > 0 and |h| < 1, which is negative. A completely positive map has a positive semidefinite Choi matrix, so no Bayesian inverse exists away from 1/2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ting-fullwood-wu-2026-three-weight-bayesian-inverse"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("pauliweightbayes-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) =>
        Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scaled(Formula c, Formula m) => Seq(c, Sp, Cdot, Sp, m);
    private static Formula Power(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat() => Seq(Complexes(), Caret, Grp(F.D(2), F.Times, Sp, F.D(2)));
    private static Formula Map() => Call("MatrixMap", Call("Fin", F.D(2)), Call("Fin", F.D(2)), Complexes());
    private static Formula Weights() => Seq(Call("Fin", F.D(4)), Sp, To, Sp, Reals());
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Sigma(Formula mu) => Call("sigma", mu);
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);

    private static Formula PaulisFormula()
    {
        Formula list = Parenthesized(Seq(
            Call("pauliMatrix", F.Id("I")), Comma, Sp, Call("pauliMatrix", F.Id("X")), Comma, Sp,
            Call("pauliMatrix", F.Id("Y")), Comma, Sp, Call("pauliMatrix", F.Id("Z"))));
        return Disp(Equal(F.Id("sigma"), list));
    }

    private static Formula ChannelFormula()
    {
        Formula p = F.Id("p"), a = F.Id("A"), mu = Mu;
        Formula term = Scaled(Apply(p, mu), TimesOf(TimesOf(Sigma(mu), a), Sigma(mu)));
        return Disp(All(p, Weights(), All(a, Mat(),
            Equal(Apply(Call("pauliChannel", p), a), SumOver(mu, term)))));
    }

    private static Formula JamFormula()
    {
        Formula n = F.Id("N"), i = F.Id("i"), j = F.Id("j");
        Formula term = Call("kronecker", Call("single", i, j, F.D(1)), Apply(n, Call("single", j, i, F.D(1))));
        return Disp(All(n, Map(), Equal(Call("jam", n), SumOver(i, SumOver(j, term)))));
    }

    private static Formula BayesFormula()
    {
        Formula e = F.Id("E"), adj = F.Id("Eadj"), f = F.Id("F");
        Formula left = Call("kronecker", Apply(e, Rho), F.D(1));
        Formula right = Call("kronecker", F.D(1), Rho);
        Formula rule = Equal(
            PlusOf(TimesOf(left, Call("jam", f)), TimesOf(Call("jam", f), left)),
            PlusOf(TimesOf(right, Call("jam", adj)), TimesOf(Call("jam", adj), right)));
        return Disp(All(e, Map(), All(adj, Map(), All(f, Map(), All(Rho, Mat(),
            Iff(Call("IsBayesianInverse", e, adj, f, Rho), And(Call("IsCPTP", f), rule)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), mu = Mu, a = F.Id("A"), b = F.Id("B"), f = F.Id("F");
        Formula channel = Call("pauliChannel", p);
        Formula nonnegative = All(mu, Call("Fin", F.D(4)), Leq(F.D(0), Apply(p, mu)));
        Formula normalized = Equal(SumOver(mu, Apply(p, mu)), F.D(1));
        Formula support = Equal(Call("card", Call("filter", Seq(mu, Sp, Mapsto, Sp, NotEqual(Apply(p, mu), F.D(0))),
            Call("univ", Call("Fin", F.D(4))))), F.D(3));
        Formula selfAdjoint = All(a, Mat(), All(b, Mat(), Equal(
            Call("trace", TimesOf(Power(a, F.Id("H")), Apply(channel, b))),
            Call("trace", TimesOf(Power(Parenthesized(Apply(channel, a)), F.Id("H")), b)))));
        Formula exists = Some(f, Map(), Call("IsBayesianInverse", channel, channel, f, Rho));
        Formula mixed = Equal(Rho, Scaled(new Formula.Fraction(F.D(1), F.D(2)), F.D(1)));
        Formula states = All(Rho, Mat(), Implies(Call("IsDensity", Rho), Iff(exists, mixed)));
        Formula body = Implies(nonnegative, Implies(normalized, Implies(support, And(selfAdjoint, states))));
        return Disp(Iff(F.Id("claim"), All(p, Weights(), body)));
    }
}
