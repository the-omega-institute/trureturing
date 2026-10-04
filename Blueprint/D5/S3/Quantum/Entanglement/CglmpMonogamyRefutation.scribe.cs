using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class CglmpMonogamyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/kumari2017sufficient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kumari, Ghose and Mann (arXiv:1704.06516, Phys. Rev. A 96, 012128) conjecture, from numerical studies, that the CGLMP inequality is monogamous for qutrits: for every three-qutrit state at most one of the reduced states rho_AB, rho_BC, rho_AC has B_CGLMP > 2, where B_CGLMP maximizes the CGLMP expression I_3 over their Fourier-phase family of measurements. It fails: for v = |002> + |011> + 2|020> + |100> + 2|112> - |121> + 2|210> + 2|222> and rho = v v^dagger / 20, both rho_AB and rho_AC reach I_3 = 1/2 + 14 sqrt 3 / 15 > 2.",
        H("Two reduced states of one three-qutrit state both violate the CGLMP inequality"),
        Blocks(
            Node("dft", "The Fourier transform", DftFormula(),
                "U_FT is the three-dimensional discrete Fourier transform, with entries omega^{jk}/sqrt 3 where omega = exp(2 pi i/3) is the existing omega; its inverse U_FT^* is the conjugate transpose.",
                "dft", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phase", "The phase matrices", PhaseFormula(),
                "U(phi) is the diagonal unitary with entries exp(-i phi(j)) for an angle vector phi : Fin 3 -> R.",
                "phase", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("joint", "Joint outcome probabilities", JointFormula(),
                "Eq. (Probabilities): applying A to the first qutrit and B to the second and measuring in the computational basis, outcome (j, k) has probability tr(Pi_j (x) Pi_k (A (x) B) rho (A^dagger (x) B^dagger)), with Pi_j = single(j, j, 1) the projector onto |j>, kronecker the Kronecker product and H the conjugate transpose.",
                "jointProb", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("event", "Event probabilities", EventFormula(),
                "The probability of an event E on the outcome pair is the sum of the joint probabilities of the outcome pairs (a, b) in E.",
                "eventProb", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("i3", "The CGLMP expression", I3Formula(),
                "Eq. (CGLMP1): I_3 = P(A_1 = B_1) + P(B_1 = A_2 + 1) + P(A_2 = B_2) + P(B_2 = A_1) - P(A_1 = B_1 - 1) - P(B_1 = A_2) - P(A_2 = B_2 - 1) - P(B_2 = A_1 - 1), with outcomes added modulo 3 in Fin 3.",
                "cglmpI3", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("at", "The CGLMP expression at given angles", AtFormula(),
                "cglmpAt(rho, theta) is I_3 of rho at the twelve angles theta = (theta_1, theta_2), with A_k = U_FT U(phi_k) for phi_k = theta_1(k) and B_l = U_FT^* U(phi'_l) for phi'_l = theta_2(l). Eq. (CGLMP2) takes B_CGLMP(rho) to be its maximum over theta.",
                "cglmpAt", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("max", "The CGLMP value of a state", IsValueFormula(),
                "Eq. (CGLMP2): b is B_CGLMP(rho) when b is the greatest value of cglmpAt(rho, theta) over all angles theta, that is, the maximum of I_3 over the twelve angles.",
                "IsCglmpValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rab", "The reduced state on AB", ReducedFormula("rhoAB", "partialTraceRight", TripleAB()),
                "For a three-qutrit matrix indexed by (a, b, c), rho_AB traces out C: the existing partialTraceRight applied to rho re-indexed by ((a, b), c) -> (a, b, c).",
                "rhoAB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rbc", "The reduced state on BC", RbcFormula(),
                "rho_BC traces out A with the existing partialTraceLeft.",
                "rhoBC", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rac", "The reduced state on AC", ReducedFormula("rhoAC", "partialTraceRight", TripleAC()),
                "rho_AC traces out B: the existing partialTraceRight applied to rho re-indexed by ((a, c), b) -> (a, b, c), so that A is measured with A_k and C with B_l.",
                "rhoAC", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured monogamy", ClaimFormula(),
                "Eq. (35): for every three-qutrit state rho_ABC, that is every positive semidefinite 27 x 27 matrix of trace one, and for the maxima b_AB, b_BC, b_AC of I_3 on rho_AB, rho_BC, rho_AC, b_AB > 2 implies b_BC <= 2 and b_AC <= 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("vec", "The counterexample vector", VecFormula(),
                "The unnormalized vector has squared norm 1 + 1 + 4 + 1 + 4 + 1 + 4 + 4 = 20; every basis state |abc> in its support has a - b - c = 1 modulo 3.",
                "stateVec", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("rho", "The counterexample state", RhoFormula(),
                "The state is the rank-one density matrix v v^dagger / 20.",
                "rho", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("ang", "The angle unit", AngFormula(),
                "Angles are integer multiples of pi/6, so every phase is a twelfth root of unity.",
                "ang", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Both reduced states violate the inequality", Disp(new Formula.Not(F.Id("claim"))),
                "Each joint probability of a reduced state of v v^dagger / 20 is one twentieth of a sum of squared amplitudes, which are sums of twelfth roots of unity divided by 3. With angles in units of pi/6, phi_1 = (0, 2, 7), phi_2 = (0, 2, 1), phi'_1 = (0, 8, 4), phi'_2 = (0, 10, 2) on rho_AB and phi_1 = (0, 6, 9), phi_2 = (0, 6, 3), phi'_1 = (0, 10, 2), phi'_2 = (0, 0, 6) on rho_AC give, in the order of Eq. (CGLMP1), the event probabilities 23/60 + sqrt 3/5, 23/60 + sqrt 3/5, 1/2, 1/2, 23/60 - sqrt 3/5, 23/60 - sqrt 3/5, 1/4 - sqrt 3/15, 1/4 - sqrt 3/15, so I_3 = 1/2 + 14 sqrt 3/15 > 2 for both. For every two-qutrit matrix, I_3 is continuous in the angles and unchanged when an angle moves by 2 pi, so it attains its maximum on the compact box [0, 2 pi]^24; each maximum of rho_AB and rho_AC is therefore at least the stated value. The state is positive semidefinite with trace one.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kumari-2017-cglmp-monogamy"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cglmp-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Of(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Fin(byte n) => Call(F.Id("Fin"), D(n));
    private static Formula Fin3() => Fin(3);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Parenthesized(Seq(a, Comma, Sp, b, Comma, Sp, c));
    private static Formula Pair3() => Seq(Fin3(), Sp, Times, Sp, Fin3());
    private static Formula Triple3() => Seq(Fin3(), Sp, Times, Sp, Fin3(), Sp, Times, Sp, Fin3());
    private static Formula Mat(Formula index) => Call(F.Id("Matrix"), index, index, Complex());
    private static Formula Ket(params byte[] digits) => Seq(Bar, D(digits), Rangle);
    private static Formula Dagger(Formula x) => Pow(x, F.Id("H"));
    private static Formula Kron(Formula a, Formula b) => Call(F.Id("kronecker"), a, b);
    private static Formula Lambda(Formula x, Formula body) => Parenthesized(Seq(x, Sp, Mapsto, Sp, body));
    private static Formula Event(Formula relation) =>
        Lambda(Pair(F.Id("a"), F.Id("b")), relation);
    private static Formula Ev(Formula rho, Formula a, Formula b, Formula relation) =>
        Call(F.Id("eventProb"), rho, a, b, Event(relation));
    private static Formula Dft() => F.Id("dft");
    private static Formula Phase(Formula angles) => Call(F.Id("phase"), angles);
    private static Formula At(Formula rho, Formula theta) => Call(F.Id("cglmpAt"), rho, theta);

    private static Formula DftFormula()
    {
        Formula j = F.Id("j"), k = F.Id("k");
        Formula entry = Frac(Pow(F.Id("omega"), Mul(Call(F.Id("val"), j), Call(F.Id("val"), k))), Root(D(3)));
        return Disp(All(j, Fin3(), All(k, Fin3(), EqTo(Of(Dft(), j, k), entry))));
    }

    private static Formula PhaseFormula()
    {
        Formula phi = Varphi, j = F.Id("j");
        Formula entry = Lambda(j, Seq(Exp, Parenthesized(Seq(Minus, Parenthesized(Mul(F.Id("i"), Of(phi, j)))))));
        return Disp(All(phi, Arrow(Fin3(), Real()),
            EqTo(Phase(phi), Call(F.Id("diagonal"), entry))));
    }

    private static Formula JointFormula()
    {
        Formula rho = Rho, a = F.Id("A"), b = F.Id("B"), j = F.Id("j"), k = F.Id("k");
        Formula proj = Kron(Call(F.Id("single"), j, j, D(1)), Call(F.Id("single"), k, k, D(1)));
        Formula product = Mul(Mul(Mul(proj, Kron(a, b)), rho), Kron(Dagger(a), Dagger(b)));
        Formula value = Call(F.Id("re"), Call(F.Id("tr"), product));
        Formula qutritMatrix = Mat(Fin3());
        return Disp(All(rho, Mat(Pair3()), All(a, qutritMatrix, All(b, qutritMatrix,
            All(j, Fin3(), All(k, Fin3(),
                EqTo(Call(F.Id("jointProb"), rho, a, b, j, k), value)))))));
    }

    private static Formula EventFormula()
    {
        Formula rho = Rho, a = F.Id("A"), b = F.Id("B"), e = F.Id("E"), x = F.Id("a"), y = F.Id("b");
        Formula condition = Seq(Of(e, x, y));
        Formula body = Seq(Sum, Underscore, Grp(Seq(x, Comma, Sp, y, Sp, Colon, Sp, condition)), Sp,
            Call(F.Id("jointProb"), rho, a, b, x, y));
        Formula qutritMatrix = Mat(Fin3());
        Formula relation = Arrow(Fin3(), Arrow(Fin3(), F.Id("Prop")));
        return Disp(All(rho, Mat(Pair3()), All(a, qutritMatrix, All(b, qutritMatrix,
            All(e, relation, EqTo(Call(F.Id("eventProb"), rho, a, b, e), body))))));
    }

    private static Formula I3Formula()
    {
        Formula rho = Rho;
        Formula a1 = new Formula.Subscript(F.Id("A"), D(1)), a2 = new Formula.Subscript(F.Id("A"), D(2));
        Formula b1 = new Formula.Subscript(F.Id("B"), D(1)), b2 = new Formula.Subscript(F.Id("B"), D(2));
        Formula x = F.Id("a"), y = F.Id("b");
        Formula plus = Add(Add(Add(Ev(rho, a1, b1, EqTo(x, y)), Ev(rho, a2, b1, EqTo(y, Add(x, D(1))))),
            Ev(rho, a2, b2, EqTo(x, y))), Ev(rho, a1, b2, EqTo(y, x)));
        Formula value = Sub(Sub(Sub(Sub(plus, Ev(rho, a1, b1, EqTo(x, Sub(y, D(1))))),
            Ev(rho, a2, b1, EqTo(y, x))), Ev(rho, a2, b2, EqTo(x, Sub(y, D(1))))),
            Ev(rho, a1, b2, EqTo(y, Sub(x, D(1)))));
        Formula qutritMatrix = Mat(Fin3());
        Formula operators = Seq(a1, Comma, Sp, a2, Comma, Sp, b1, Comma, Sp, b2);
        return Disp(All(rho, Mat(Pair3()), All(operators, qutritMatrix,
            EqTo(Call(F.Id("cglmpI3"), rho, a1, a2, b1, b2), value))));
    }

    private static Formula AtFormula()
    {
        Formula rho = Rho, theta = Theta;
        Formula t1 = new Formula.Subscript(theta, D(1)), t2 = new Formula.Subscript(theta, D(2));
        Formula i3 = Call(F.Id("cglmpI3"), rho, Mul(Dft(), Phase(Of(t1, D(0)))), Mul(Dft(), Phase(Of(t1, D(1)))),
            Mul(Dagger(Dft()), Phase(Of(t2, D(0)))), Mul(Dagger(Dft()), Phase(Of(t2, D(1)))));
        Formula angles = Arrow(Fin(2), Arrow(Fin3(), Real()));
        Formula pair = Seq(Parenthesized(angles), Sp, Times, Sp, Parenthesized(angles));
        Formula thetaPair = Pair(t1, t2);
        return Disp(All(rho, Mat(Pair3()), All(thetaPair, pair,
            EqTo(Call(F.Id("cglmpAt"), rho, thetaPair), i3))));
    }

    private static Formula TripleAB() =>
        Lambda(Pair(Pair(F.Id("a"), F.Id("b")), F.Id("c")), Triple(F.Id("a"), F.Id("b"), F.Id("c")));

    private static Formula TripleAC() =>
        Lambda(Pair(Pair(F.Id("a"), F.Id("c")), F.Id("b")), Triple(F.Id("a"), F.Id("b"), F.Id("c")));

    private static Formula ReducedFormula(string name, string trace, Formula reindex)
    {
        Formula rho = Rho;
        Formula reindexed = Call(F.Id("submatrix"), rho, reindex, reindex);
        return Disp(All(rho, Mat(Triple3()),
            EqTo(Call(F.Id(name), rho), Call(F.Id(trace), reindexed))));
    }

    private static Formula RbcFormula()
    {
        Formula rho = Rho;
        return Disp(All(rho, Mat(Triple3()),
            EqTo(Call(F.Id("rhoBC"), rho), Call(F.Id("partialTraceLeft"), rho))));
    }

    private static Formula ClaimFormula()
    {
        Formula rho = Rho;
        Formula bab = new Formula.Subscript(F.Id("b"), F.Id("AB"));
        Formula bbc = new Formula.Subscript(F.Id("b"), F.Id("BC"));
        Formula bac = new Formula.Subscript(F.Id("b"), F.Id("AC"));
        Formula hypotheses = Logic(Call(F.Id("PosSemidef"), rho), FormulaLogicOperator.And,
            EqTo(Call(F.Id("tr"), rho), D(1)));
        Formula maxima = Logic(Logic(Call(F.Id("IsCglmpValue"), Call(F.Id("rhoAB"), rho), bab),
            FormulaLogicOperator.And, Call(F.Id("IsCglmpValue"), Call(F.Id("rhoBC"), rho), bbc)),
            FormulaLogicOperator.And, Call(F.Id("IsCglmpValue"), Call(F.Id("rhoAC"), rho), bac));
        Formula violation = Rel(D(2), FormulaRelationOperator.LessThan, bab);
        Formula others = Logic(LeTo(bbc, D(2)), FormulaLogicOperator.And, LeTo(bac, D(2)));
        Formula scalars = Seq(bab, Comma, Sp, bbc, Comma, Sp, bac);
        Formula body = Imp(hypotheses, All(scalars, Real(), Imp(maxima, Imp(violation, others))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(rho, Mat(Triple3()), body)));
    }

    private static Formula IsValueFormula()
    {
        Formula rho = Rho, b = F.Id("b"), theta = Theta;
        Formula angles = Seq(Parenthesized(Arrow(Fin(2), Arrow(Fin3(), Real()))), Sp, Times, Sp,
            Parenthesized(Arrow(Fin(2), Arrow(Fin3(), Real()))));
        Formula attained = Seq(Exists, Sp, theta, Sp, Colon, Sp, angles, Comma, Sp, EqTo(At(rho, theta), b));
        Formula bound = All(theta, angles, LeTo(At(rho, theta), b));
        Formula body = Logic(Call(F.Id("IsCglmpValue"), rho, b), FormulaLogicOperator.Iff,
            Logic(attained, FormulaLogicOperator.And, bound));
        return Disp(All(rho, Mat(Pair3()), All(b, Real(), body)));
    }

    private static Formula VecFormula()
    {
        Formula sum = Add(Add(Add(Add(Add(Add(Add(Ket(0, 0, 2), Ket(0, 1, 1)), Mul(D(2), Ket(0, 2, 0))),
            Ket(1, 0, 0)), Mul(D(2), Ket(1, 1, 2))), Seq(Minus, Ket(1, 2, 1))), Mul(D(2), Ket(2, 1, 0))),
            Mul(D(2), Ket(2, 2, 2)));
        return Disp(EqTo(F.Id("stateVec"), sum));
    }

    private static Formula RhoFormula()
    {
        Formula v = F.Id("stateVec");
        return Disp(EqTo(F.Id("rho"), Mul(Frac(D(1), D(2, 0)), Call(F.Id("vecMulVec"), v, Call(F.Id("star"), v)))));
    }

    private static Formula AngFormula()
    {
        Formula n = F.Id("n");
        return Disp(All(n, NumberSet(F.Id("N")), EqTo(Call(F.Id("ang"), n), Frac(Mul(n, Pi), D(6)))));
    }
}
