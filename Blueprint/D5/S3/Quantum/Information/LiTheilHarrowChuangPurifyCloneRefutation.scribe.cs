using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class LiTheilHarrowChuangPurifyCloneRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/litheilharrowchuang2026coherent");
    private const string Conjecture = "Section S3 A, p. 9: “This channel is optimal for m ≤ n (see Ref. [S2]), and we conjecture that it is also optimal for m > n.” The formula takes n = 1 and m = 2 and the worst-case one-site infidelity interpretation. Both system and environment registers belong to each site. The dimensions satisfy 1 ≤ r ≤ d, and all input states of rank at most r occur.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A symmetric quantum channel has one-site worst-case infidelity at most one sixth, while purify-and-clone has risk at least one fifth in system and environment dimension two.",
        H("Purify-and-clone is not optimal for one-site worst-case risk"),
        Blocks(
            Node("sqFidelity", FidelityFormula(), "Squared Uhlmann fidelity is (Tr √(√α β √α))². The formula uses the real part of the trace of the positive square root.", AssessedProvenance.FromLiterature(Source)),
            Node("purifications", PurificationsFormula(), "Section S3 A, p. 8: “That is, C(ρ) is the convex hull of all m-tensor powers of purifications of ρ.” Here purifications r rho is the set of trace-one positive rank-one matrices whose environment partial trace is rho. The range of the conversion from DensityState is exactly the set of ordinary density matrices.", AssessedProvenance.FromLiterature(Source)),
            Node("oneSiteMarginal", MarginalFormula(), "The two choices retain the first and second joint system-environment sites. The environment inside a retained site is not discarded.", AssessedProvenance.FromLiterature(Source)),
            Node("oneSiteLoss", LossFormula(), "Equation (S13), p. 5, takes the infimum over one common gamma in conv(c(Sigma)) before the maximum over the sites. For two sites the maximum has two entries. The real infidelities are embedded into EReal before taking the infimum.", AssessedProvenance.FromLiterature(Source)),
            Node("worstCaseOneSiteRisk", RiskFormula(), "Equation (7) specializes to the supremum of the one-site losses over every density matrix of rank at most r. The risk is defined for arbitrary matrix maps; the optimality statement restricts the competitors to QuantumChannel.", AssessedProvenance.FromLiterature(Source)),
            Node("TotallySymmetricSupport", SupportFormula(), "The output lies in the symmetric subspace on both sides: S Xi S = Xi. Invariance under conjugation by the swap alone is insufficient.", AssessedProvenance.FromLiterature(Source)),
            Node("wernerOneToTwo", WernerFormula(), "The one-to-two pure-state cloning channel in equation (S35) has coefficient 2/(D+1), with D equal to the cardinality of the input index type.", AssessedProvenance.FromLiterature(Source)),
            Node("randomPurifyOne", PurifyFormula(), "Equations (S37c) and (S38), p. 9, specialize at one input to rho tensor I/r, obtained by averaging the environment of a purification.", AssessedProvenance.FromLiterature(Source)),
            Node("purifyAndClone", ChannelFormula(), "Equation (S35) at n = 1 and m = 2 first applies randomPurifyOne, then the Werner cloner in dimension d r.", AssessedProvenance.FromLiterature(Source)),
            Node("AdmissibleChannel", AdmissibleFormula(), "Section S3 A, p. 8 restricts the output to the totally symmetric subspace of the joint system and environment sites. This restriction holds for every density input of rank at most r.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("lthc-rank-positive-trace-one"), DeclarationHandle.Create(Prefix + "rank_pos_of_trace_one"), H("Positive rank of a trace-one matrix"), StatementSource.FromAuthor(Disp(Generic(All("A", Mat(V("a")), Imp(Eqn(Trace(V("A")), D(1)), Rel(D(0), FormulaRelationOperator.LessThan, Rank(V("A")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A trace-one complex matrix has positive rank."))), DescribeRole.Theorem),
            Node("claim", Iff(C("claim"), ClaimBody()), Conjecture, AssessedProvenance.FromLiterature(Source)),
            Node("result", new Formula.Not(Parenthesized(ClaimBody())), "In dimension d = r = 2, clone the system with the two-dimensional Werner cloner and tensor its output with one third of the symmetric environment projector, then reorder the registers into two sites. Its Kraus operators give a completely positive trace-preserving channel. Both-sided symmetric support holds. A four-element Pauli average puts rho tensor I/2 in the common target convex hull for every input. Matrix square-root order gives fidelity at least 5/6 for this channel. For the pure zero input, every target has fidelity at most 4/5 with the purify-and-clone marginal. Thus the respective worst-case risks are at most 1/6 and at least 1/5. The universal inequality fails. The all-site and average risks and a strict-improvement family in arbitrary dimensions are not asserted.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("li-theil-harrow-chuang-2026-purify-and-clone-optimality"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("lthc-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(params string[] names) => Seq([.. names.SelectMany((name, i) => i == 0 ? new Formula[] { Operatorname, Grp(V(name)) } : [Dot, Operatorname, Grp(V(name))])]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Some(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Field(string s) => Seq(Mathbb, Grp(V(s)));
    private static Formula Fin(Formula n) => C("Fin", n);
    private static Formula ProdType(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Site(Formula d, Formula r) => ProdType(Fin(d), Fin(r));
    private static Formula Out(Formula d, Formula r) => ProdType(Site(d, r), Site(d, r));
    private static Formula Mat(Formula a) => C("Matrix", a, a, Field("C"));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lambda(string n, Formula type, Formula body) => Seq(Operatorname, Grp(V("fun")), Sp, Parenthesized(Seq(V(n), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string n, Formula type, Formula body) => Seq(OpenBrace, Sp, V(n), Sp, Colon, Sp, type, Sp, Mid, Sp, Parenthesized(body), Sp, CloseBrace);
    private static Formula Raw(Formula rho) => At(Q("CStarMatrix", "ofMatrix", "symm"), C("val", rho));
    private static Formula Trace(Formula x) => At(Q("Matrix", "trace"), x);
    private static Formula Root(Formula x) => At(Q("CFC", "sqrt"), x);
    private static Formula RealPart(Formula x) => At(Q("Complex", "re"), x);
    private static Formula Rank(Formula x) => At(Q("Matrix", "rank"), x);
    private static Formula Kron(Formula x, Formula y) => At(Q("Matrix", "kronecker"), x, y);
    private static Formula State(Formula a) => C("DensityState", a);
    private static Formula Channel(Formula d, Formula r) => C("QuantumChannel", Fin(d), Out(d, r));
    private static Formula Action(Formula phi, Formula x) => At(Q("CStarMatrix", "ofMatrix", "symm"), At(Q("QuantumChannel", "toCompletelyPositiveMap"), phi, At(Q("CStarMatrix", "ofMatrix"), x)));
    private static Formula Instances(Formula a, Formula body) => Seq(OpenBracket, C("Fintype", a), CloseBracket, Sp, OpenBracket, C("DecidableEq", a), CloseBracket, Comma, Sp, body);
    private static Formula Generic(Formula body) => All("a", C("Type"), Instances(V("a"), body));
    private static Formula Dimensions(Formula body) => All("d", Field("N"), All("r", Field("N"), body));

    private static Formula FidelityFormula()
    {
        Formula a = V("a"), alpha = V("alpha"), beta = V("beta");
        return Generic(All("alpha", Mat(a), All("beta", Mat(a), Eqn(C("sqFidelity", alpha, beta), new Formula.Power(RealPart(Trace(Root(Mul(Mul(Root(alpha), beta), Root(alpha))))), D(2))))));
    }
    private static Formula PurificationsFormula()
    {
        Formula d = V("d"), r = V("r"), rho = V("rho"), psi = V("Psi"), site = Site(d, r);
        Formula range = At(Q("Set", "range"), Lambda("sigma", State(site), Raw(V("sigma"))));
        return Dimensions(All("rho", State(Fin(d)), Eqn(C("purifications", r, rho), SetOf("Psi", Mat(site), And(Mem(psi, range), And(Eqn(Rank(psi), D(1)), Eqn(C("partialTraceRight", psi), Raw(rho))))))));
    }
    private static Formula MarginalFormula()
    {
        Formula d = V("d"), r = V("r"), xi = V("Xi"), i = V("i");
        Formula rhs = Seq(Operatorname, Grp(V("if")), Sp, Parenthesized(Eqn(i, D(0))), Sp, Operatorname, Grp(V("then")), Sp, C("partialTraceRight", xi), Sp, Operatorname, Grp(V("else")), Sp, C("partialTraceLeft", xi));
        return Dimensions(All("Xi", Mat(Out(d, r)), All("i", Fin(D(2)), Eqn(C("oneSiteMarginal", xi, i), rhs))));
    }
    private static Formula LossFormula()
    {
        Formula d = V("d"), r = V("r"), rho = V("rho"), xi = V("Xi"), gamma = V("gamma");
        Formula f = Lambda("gamma", Mat(Site(d, r)), Parenthesized(Seq(Parenthesized(Seq(C("max", Sub(D(1), C("sqFidelity", gamma, C("oneSiteMarginal", xi, D(0)))), Sub(D(1), C("sqFidelity", gamma, C("oneSiteMarginal", xi, D(1))))), Sp, Colon, Sp, Field("R"))), Sp, Colon, Sp, C("EReal"))));
        Formula targets = C("convexHull", Field("R"), C("purifications", r, rho));
        return Dimensions(All("rho", State(Fin(d)), All("Xi", Mat(Out(d, r)), Eqn(C("oneSiteLoss", rho, xi), C("sInf", At(Q("Set", "image"), f, targets))))));
    }
    private static Formula RiskFormula()
    {
        Formula d = V("d"), r = V("r"), t = V("T"), rho = V("rho"), x = V("x");
        Formula set = SetOf("x", C("EReal"), Some("rho", State(Fin(d)), And(Leq(Rank(Raw(rho)), r), Eqn(x, C("oneSiteLoss", rho, At(t, Raw(rho)))))));
        return Dimensions(All("T", Arrow(Mat(Fin(d)), Mat(Out(d, r))), Eqn(C("worstCaseOneSiteRisk", t), C("sSup", set))));
    }
    private static Formula Projector(Formula a) => Smul(Div(D(1), D(2)), Add(D(1), At(Q("Equiv", "Perm", "permMatrix"), Field("C"), At(Q("Equiv", "prodComm"), a, a))));
    private static Formula SupportFormula()
    {
        Formula a = V("a"), xi = V("Xi"), s = Projector(a);
        return Generic(All("Xi", Mat(ProdType(a, a)), Iff(C("TotallySymmetricSupport", xi), Eqn(Mul(Mul(s, xi), s), xi))));
    }
    private static Formula WernerFormula()
    {
        Formula a = V("a"), x = V("X"), s = Projector(a);
        return Generic(All("X", Mat(a), Eqn(C("wernerOneToTwo", x), Smul(Div(D(2), Add(Parenthesized(Seq(At(Q("Fintype", "card"), a), Sp, Colon, Sp, Field("C"))), D(1))), Mul(Mul(s, Kron(x, D(1))), s)))));
    }
    private static Formula PurifyFormula()
    {
        Formula d = V("d"), r = V("r"), x = V("X");
        return Dimensions(All("X", Mat(Fin(d)), Eqn(C("randomPurifyOne", r, x), Kron(x, Smul(Seq(Parenthesized(Seq(r, Sp, Colon, Sp, Field("C"))), Caret, Grp(Minus, D(1))), D(1))))));
    }
    private static Formula ChannelFormula()
    {
        Formula d = V("d"), r = V("r"), x = V("X");
        return Dimensions(All("X", Mat(Fin(d)), Eqn(C("purifyAndClone", d, r, x), C("wernerOneToTwo", C("randomPurifyOne", r, x)))));
    }
    private static Formula AdmissibleFormula()
    {
        Formula d = V("d"), r = V("r"), phi = V("Phi"), rho = V("rho");
        return Dimensions(All("Phi", Channel(d, r), Iff(C("AdmissibleChannel", phi), All("rho", State(Fin(d)), Imp(Leq(Rank(Raw(rho)), r), C("TotallySymmetricSupport", Action(phi, Raw(rho))))))));
    }
    private static Formula ClaimBody()
    {
        Formula d = V("d"), r = V("r"), phi = V("Phi");
        return Dimensions(Imp(Leq(D(1), r), Imp(Leq(r, d), All("Phi", Channel(d, r), Imp(C("AdmissibleChannel", phi), Leq(C("worstCaseOneSiteRisk", C("purifyAndClone", d, r)), C("worstCaseOneSiteRisk", Lambda("X", Mat(Fin(d)), Action(phi, V("X"))))))))));
    }
}
