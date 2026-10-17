using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class PauliThreeWeightBayesianInverseUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/ting2026operational");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ting, Fullwood and Wu (arXiv:2605.10375) characterize when a unital qubit channel has a Bayesian inverse with respect to a state, and for Pauli channels with exactly three non-zero weights leave open whether the maximally mixed state is the only such state. It is: for every Pauli channel whose probability vector has exactly three non-zero entries, a completely positive trace-preserving Bayesian inverse with respect to a qubit state exists if and only if the state is the maximally mixed state.",
        H("Three-weight Pauli channels have Bayesian inverses only at the maximally mixed state"),
        Blocks(
            Node("paulis", "The Pauli matrices", PaulisFormula(),
                "sigma lists the identity and the Pauli matrices X, Y = i X Z and Z of pauliMatrix, indexed by Fin 4.",
                "sigma", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-properties", "Self-adjoint Pauli involutions", SigmaPropertiesFormula(),
                "Each of the four Pauli matrices is self-adjoint and its square is the identity. "
                    + "The superscript H denotes conjugate transpose, and the product is matrix multiplication.",
                "sigma_properties", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("spin", "Spin observables", SpinFormula(),
                "For every real three-vector r, spin r is the sum of the complex embeddings of its coordinates times the three Pauli matrices. The index i.succ in Fin 4 selects X, Y and Z, leaving out the identity.",
                "spin", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("channel", "The Pauli channel", ChannelFormula(),
                "The Pauli channel with probability vector p acts by A -> sum over mu of p_mu sigma_mu A sigma_mu, as a complex-linear map on 2 x 2 matrices.",
                "pauliChannel", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("channel-cptp", "Complete positivity and trace preservation", ChannelCptpFormula(),
                "Every nonnegative normalized vector of four Pauli weights gives a completely positive trace-preserving map.",
                "channel_cptp", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
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
                "At the maximally mixed state the channel itself is a Bayesian inverse: it is completely positive with Kraus operators sqrt(p_mu) sigma_mu, trace preserving, and both sides of the Bayes rule equal J of the channel because the channel fixes 1/2. Conversely, write rho = (1 + r . sigma)/2 with sum r_i^2 <= 1 and r ≠ 0. The exact Bayes rule becomes a Sylvester equation for the canonical output-input Choi matrix C = MatrixMap.choi_matrix F. With s_i = lambda_i r_i, V = 1 tensor (s . sigma)^T and R = {rho tensor 1, MatrixMap.choi_matrix E}, one has V^2 = |s|^2 1 and C + (VC + CV)/2 = R. Therefore D C = (1 - |s|^2/2) R - (VR + RV)/2 + VRV/2, where D = 1 - |s|^2 >= 0. If p_k is the zero weight, let a_1, a_2, a_3 be the other three weights, listed through the Pauli product table, and h_i = (1 - a_i) r_i. The vector w(j, i) = ((1 - h . sigma) sigma_k)_{j i}, indexed by output j and input i, gives w* (D C) w = -4[(1 - |h|^2) B + K A], with A = sum a_i h_i^2, B = sum a_i^2 (1 - a_i) r_i^2 and K = sum a_i^2 r_i^2. Here B > 0 and |h| < 1, so the value is negative for every nonzero r, including pure states and every missing-weight position. The owning Choi theorem MatrixMap.choi_PSD_iff_CP_map makes C positive semidefinite under complete positivity, and multiplication by D >= 0 preserves this property, giving a contradiction. No division by D is used. The strict estimate |lambda_i| < 1 available for three positive weights also gives D > 0, uniqueness of the Sylvester candidate, and the equivalent divided expression w* C w = -4[(1 - |h|^2) B + K A]/D; those strict-denominator consequences are explanatory algebra, while the Lean obstruction uses only D >= 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ting-fullwood-wu-2026-three-weight-bayesian-inverse"),
                    ResolutionKind.Proved)),
            Paragraph(Text("Proposition 1 of the cited source transports Bayesian inverses under N = U composed with E composed with V: the state becomes V^dagger(rho) and the inverse becomes V^dagger composed with F composed with U^dagger. Unitary conjugation fixes 1/2 in both directions, so the Pauli conclusion applies to a unital qubit channel whose associated Pauli channel has three nonzero weights. This application uses the published proposition; unitary transport is not part of the Lean result. Operational reversal concerns the sequential measurement correlations in the exact Bayes rule. It asserts neither physical inversion of noise on arbitrary states nor a bound on resources for realizing the inverse.")),
            Paragraph(Text("For one nonzero weight the channel is unitary and every state has a Bayesian inverse; for two weights the source gives a coordinate axis of such states. Four positive weights permit a neighbourhood of 1/2 by positivity of the channel Choi matrix and continuity of the candidate, whereas at three weights the missing Pauli gives a zero Bell eigenvalue and the explicit quadratic form excludes every nonzero Bloch vector. The general four-weight inequalities and the continuity argument are outside the Lean result, as are exhaustive novelty and experimental implementation claims."))),
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

    private static Formula SigmaPropertiesFormula()
    {
        Formula matrix = Sigma(Mu);
        return Disp(All(Mu, Call("Fin", F.D(4)), And(
            Equal(Power(Parenthesized(matrix), F.Id("H")), matrix),
            Equal(TimesOf(matrix, matrix), F.D(1)))));
    }

    private static Formula Qualified(params string[] parts)
    {
        Formula result = Named(parts[0]);
        for (var i = 1; i < parts.Length; i++)
            result = Seq(result, Dot, Named(parts[i]));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified([.. owner.Split('.'), name]), [.. arguments]);

    private static Formula SpinFormula()
    {
        Formula r = F.Id("r"), i = F.Id("i");
        const string owner = "D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness";
        Formula direction = new Formula.TypeArrow(Call("Fin", F.D(3)), Reals());
        Formula term = Scaled(QCall("Complex", "ofReal", Apply(r, i)),
            QCall(owner, "sigma", QCall("Fin", "succ", i)));
        Formula sum = Seq(Sum, Underscore, Grp(Seq(i, Colon, Sp, Call("Fin", F.D(3)))),
            Sp, Parenthesized(term));
        return Disp(All(r, direction, Equal(QCall(owner, "spin", r), sum)));
    }

    private static Formula ChannelFormula()
    {
        Formula p = F.Id("p"), a = F.Id("A"), mu = Mu;
        Formula term = Scaled(Apply(p, mu), TimesOf(TimesOf(Sigma(mu), a), Sigma(mu)));
        return Disp(All(p, Weights(), All(a, Mat(),
            Equal(Apply(Call("pauliChannel", p), a), SumOver(mu, term)))));
    }

    private static Formula ChannelCptpFormula()
    {
        Formula p = F.Id("p"), mu = Mu;
        Formula nonnegative = All(mu, Call("Fin", F.D(4)), Leq(F.D(0), Apply(p, mu)));
        Formula normalized = Equal(SumOver(mu, Apply(p, mu)), F.D(1));
        return Disp(All(p, Weights(), Implies(nonnegative, Implies(normalized,
            Call("IsCPTP", Call("pauliChannel", p))))));
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
        Formula states = All(Rho, Mat(), Implies(Call("IsDensity", Rho), Iff(Parenthesized(exists), mixed)));
        Formula body = Implies(nonnegative, Implies(normalized, Implies(support, And(selfAdjoint, states))));
        return Disp(Iff(F.Id("claim"), All(p, Weights(), body)));
    }
}
