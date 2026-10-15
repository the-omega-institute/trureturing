using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class IsolatedQubitEnsembleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/kechrimparisbae2020omp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-state qubit ensemble with unequal positive priors has a unique minimum-error POVM. Every completely positive trace-preserving channel sharing an optimal POVM with this ensemble is the identity.",
        H("An isolated qubit ensemble"),
        Blocks(
            Node("optimal", "Minimum-error optimality", "IsOptimalPOVM", OptimalFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "The goal of minimum error state discrimination is to find the measurement strategy that minimizes the error in guessing the states of a known ensemble correctly, or equivalently, to find the strategy that maximizes the probability of guessing correctly on average. (arXiv PDF, p. 2.) For n labels in Fin n, q gives the real priors and rho gives complex two-by-two matrices. The predicate requires M to be a POVM and compares its success probability with every POVM F on the same labels. Positivity and normalization of the ensemble are separate hypotheses of the assertion below. Matrix.trace(rho(i) * F(i)).re is the real success contribution."),
            Node("omp", "Optimal measurement preservation", "IsOMP", OmpFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "Definition 1 (arXiv PDF, pp. 2–3): We call a channel 𝒩 optimal measurement preserving (OMP) for an ensemble of states S={qₓ,ρₓ}ⁿₓ₌₁, if an optimal measurement before and after a channel use is the same. The encoding asks for one POVM M optimal both for rho and for the family i maps to N(rho(i)); N is a complex-linear matrix map. Complete positivity and trace preservation are imposed where channels are quantified."),
            Node("isolated", "Isolation", "IsIsolated", IsolatedFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "Conclusions (arXiv PDF, p. 11): The first concerns the existence of ensembles whose OMP sets are all trivial. This would imply that such ensembles are isolated in that any CPTP map acting on them necessarily changes all optimal measurements. Trivial here means that the OMP set contains only the identity. Thus every CPTP map N sharing an optimal POVM with the original ensemble must equal LinearMap.id."),
            Node("claim", "The expectation that no isolated ensembles exist", "claim", ClaimFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "Conclusions (arXiv PDF, p. 11): We expect that no isolated ensembles exist but we have not managed to establish the result in general. The assertion ranges over every natural number n, every strictly positive normalized real prior family on Fin n, and every family of positive semidefinite complex two-by-two matrices of trace one. It says that each such ensemble fails IsIsolated. Zero-outcome families cannot satisfy the normalization hypothesis."),
            Node("result", "Four states refute the expectation", "result", new Formula.Not(V("claim")),
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                "Set G=19 and use the priors (9,9,5,5)/28. Let the four Pauli directions be (3/5,0,4/5), (-3/5,0,4/5), (0,3/5,-4/5), (0,-3/5,-4/5). Write S(i) for the corresponding Pauli matrix. The first two states are (I-S(i)/18)/2; the last two are (I-9S(i)/10)/2. The effects (I-S(i))/4 are positive and sum to I. The dual matrix 19 I/112 has positive slacks of weights 1/56,1/56,9/56,9/56. Equality in the score bound forces each effect into the one-dimensional slack kernel; completeness fixes their weights, giving a unique optimum.",
                "For a channel preserving this optimum, positive quadratic perturbations of individual effects give eight stationarity equalities. The state family spans all two-by-two complex matrices, so these equalities determine the channel on the entire matrix space. Its affine Bloch linear part has diagonal entries 1-9 epsilon, 1-epsilon, 1-9 epsilon/5+tZ and third-column entries tX,tY. Positivity of the Choi matrix forces epsilon=0, followed by tZ=tX=tY=0. The only preserving CPTP channel is therefore the identity, and the positive normalized ensemble contradicts claim.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        AssessedProvenance provenance, DescribeRole role, params string[] prose) =>
        Describe.Lean(DescribeId.Create("kb-isolation-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(prose.Select(p => Paragraph(Text(p))).ToArray()), role,
            declaration == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("kechrimparis-bae-2020-isolated-qubit-ensembles"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat() => Call("Matrix", Fin(D(2)), Fin(D(2)), Field("C"));
    private static Formula Map() => Call("MatrixMap", Fin(D(2)), Fin(D(2)), Field("C"));
    private static Formula Fun(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Eq(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumOver(string name, Formula type, Formula value) =>
        Seq(Sum, Underscore, Grp(V(name), Sp, Colon, Sp, type), Sp, Parenthesized(value));
    private static Formula Score(Formula n, Formula q, Formula rho, Formula measurement) =>
        SumOver("i", Fin(n), Mul(App(q, V("i")),
            Seq(App(Qualified("Matrix", "trace"), Mul(App(rho, V("i")), App(measurement, V("i")))), Dot, V("re"))));
    private static Formula Families(Formula body) =>
        All("n", Field("N"), All("q", Fun(Fin(V("n")), Field("R")),
            All("rho", Fun(Fin(V("n")), Mat()), body)));

    private static Formula OptimalFormula()
    {
        Formula n=V("n"), q=V("q"), rho=V("rho"), m=V("M"), f=V("F");
        return Families(All("M", Fun(Fin(n), Mat()),
            Iff(Call("IsOptimalPOVM", q, rho, m), And(Call("IsPOVM", m),
                All("F", Fun(Fin(n), Mat()), Imp(Call("IsPOVM", f),
                    Rel(Score(n,q,rho,f), FormulaRelationOperator.LessThanOrEqual, Score(n,q,rho,m))))))));
    }
    private static Formula OmpFormula()
    {
        Formula n=V("n"), q=V("q"), rho=V("rho"), m=V("M"), channel=V("N");
        Formula images=Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Colon, Sp, Fin(n), Sp, Mapsto, Sp,
            App(channel, App(rho,V("i")))));
        return Families(All("N", Map(), Iff(Call("IsOMP",q,rho,channel),
            Ex("M", Fun(Fin(n),Mat()), And(Call("IsOptimalPOVM",q,rho,m), Call("IsOptimalPOVM",q,images,m))))));
    }
    private static Formula IsolatedFormula()
    {
        Formula q=V("q"), rho=V("rho"), channel=V("N");
        return Families(Iff(Call("IsIsolated",q,rho), All("N",Map(),
            Imp(Call("IsCPTP",channel),Imp(Call("IsOMP",q,rho,channel),Eq(channel,Qualified("LinearMap","id")))))));
    }
    private static Formula ClaimFormula()
    {
        Formula n=V("n"), q=V("q"), rho=V("rho");
        Formula positive=All("i",Fin(n),Rel(D(0),FormulaRelationOperator.LessThan,App(q,V("i"))));
        Formula normalized=Eq(SumOver("i",Fin(n),App(q,V("i"))),D(1));
        Formula states=All("i",Fin(n),Call("IsDensity",App(rho,V("i"))));
        return Iff(V("claim"),Families(Imp(positive,Imp(normalized,Imp(states,new Formula.Not(Call("IsIsolated",q,rho)))))));
    }
}
