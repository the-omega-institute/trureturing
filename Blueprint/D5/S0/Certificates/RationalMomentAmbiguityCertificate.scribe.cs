using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalMomentAmbiguityCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/RationalMomentAmbiguityCertificate.";
    private static Formula Z => F.D(0);
    private static Formula One => F.D(1);
    private static Formula Feature => V("feature");
    private static Formula Query => V("query");
    private static Formula Tol => V("tolerance");
    private static Formula High => V("high");
    private static Formula Low => V("low");
    private static Formula Env => V("envelope");
    private static Formula Cert => V("certificate");
    private static Formula CE => Call("envelope", Cert);
    private static Formula CH => Call("high", Cert);
    private static Formula CL => Call("low", Cert);
    private static Formula Valid => Call("ValidContactCertificate", Feature, Query, Tol, Cert);
    private static Formula Check => Call("checkContactCertificate", Feature, Query, Tol, Cert);
    private static Formula B(Formula e) => Call("residualBudget", Tol, e);
    private static Formula E(Formula e) => Call("queryResidual", Feature, Query, e, V("i"));
    private static Formula Coef(Formula e) => Call("coefficient", e, V("j"));
    private static Formula Objective(Formula w) => Call("linearObjective", Query, w);
    private static Formula Pair(Formula h, Formula l) => Call("MomentTolerancePair", Feature, Tol, h, l);
    private static Formula Global(Formula e) => Call("GlobalQueryEnvelope", Feature, Query, e);
    private static Formula DeltaMoment(Formula h, Formula l) => R(
        Call("linearObjective", P(Seq(LambdaLower, Sp, V("i"), Sp, Mapsto, Sp, Call("feature", V("i"), V("j")))), h), Minus,
        Call("linearObjective", P(Seq(LambdaLower, Sp, V("i"), Sp, Mapsto, Sp, Call("feature", V("i"), V("j")))), l));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational contacts certify an attained largest query difference and an attained least residual budget. Support-monotone compression preserves their optimality.",
        H("Moment ambiguity and exact contact certificates"),
        Blocks(
            Paragraph(Text("All coefficients are rational. Feature has type Fin n to Fin d to Q; query and the two weights have type Fin n to Q; tolerance and predictor coefficients have type Fin d to Q. Indices i and j range over Fin n and Fin d respectively. Named applications also denote structure-field access.")),
            Describe.Lean(DescribeId.Create("moment-tolerance-pair"), DeclarationHandle.Create(Prefix + "MomentTolerancePair"), H("Two probability laws with moment tolerances"),
                StatementSource.FromAuthor(Disp(All("n d feature tolerance high low", R(Pair(High, Low), Leftrightarrow, And(
                    All("i", R(Z, Le, Call("high", V("i")))), R(S("i", Call("high", V("i"))), Eq, One),
                    All("i", R(Z, Le, Call("low", V("i")))), R(S("i", Call("low", V("i"))), Eq, One),
                    All("j", R(Abs(DeltaMoment(High, Low)), Le, Call("tolerance", V("j"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Tolerances compare the two models directly. The laws have separate nonnegativity and normalization conditions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("global-query-envelope"), DeclarationHandle.Create(Prefix + "GlobalQueryEnvelope"), H("Envelope on every allowed atom"),
                StatementSource.FromAuthor(Disp(All("n d feature query envelope", R(Global(Env), Leftrightarrow, All("i", And(
                    R(Call("lower", Env), Le, E(Env)), R(E(Env), Le, Call("upper", Env)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The check covers the whole carrier, including atoms absent from both proposed witnesses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moment-tolerance-cost"), DeclarationHandle.Create(Prefix + "momentToleranceCost"), H("Slope-weighted uncertainty cost"),
                StatementSource.FromAuthor(Disp(All("d tolerance envelope", R(Call("momentToleranceCost", Tol, Env), Eq,
                    S("j", R(Abs(Coef(Env)), Cdot, Call("tolerance", V("j")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Absolute predictor slopes weight the coordinatewise moment tolerances."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-budget"), DeclarationHandle.Create(Prefix + "residualBudget"), H("Width plus uncertainty"),
                StatementSource.FromAuthor(Disp(All("d tolerance envelope", R(B(Env), Eq,
                    R(R(Call("upper", Env), Minus, Call("lower", Env)), Plus, Call("momentToleranceCost", Tol, Env)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the dual value compared against all admissible query differences."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("query-gap-bound"), DeclarationHandle.Create(Prefix + "query_gap_le_residualBudget"), H("Uniform query bound"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance high low envelope", R(
                    And(Pair(High, Low), Global(Env)), Rightarrow, R(Abs(R(Objective(High), Minus, Objective(Low))), Le, B(Env)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing expectation enclosure is applied to both laws, then their predictor-center difference is bounded using the nominated moment errors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primal-dual-gap"), DeclarationHandle.Create(Prefix + "primal_dual_gap_identity"), H("Exact three-part gap identity"),
                StatementSource.FromAuthor(Disp(GapFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity requires only normalization. Under pair and global-envelope feasibility its upper-contact, lower-contact and signed-moment contributions are all nonnegative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-data"), DeclarationHandle.Create(Prefix + "ContactCertificate"), H("Data-only certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The structure has exactly high : Fin n to Q, low : Fin n to Q, and envelope : QueryEnvelope d. There are no proof fields."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid-contact"), DeclarationHandle.Create(Prefix + "ValidContactCertificate"), H("Contact and alignment conditions"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance certificate", R(Valid, Leftrightarrow, And(
                    Pair(CH, CL), Global(CE),
                    All("i", R(R(Call("high", Cert, V("i")), Neq, Z), Rightarrow, R(E(CE), Eq, Call("upper", CE)))),
                    All("i", R(R(Call("low", Cert, V("i")), Neq, Z), Rightarrow, R(E(CE), Eq, Call("lower", CE)))),
                    All("j", R(R(Coef(CE), Cdot, P(DeltaMoment(CH, CL))), Eq, R(Abs(Coef(CE)), Cdot, Call("tolerance", V("j")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The high support touches the upper residual level and the low support the lower level. Predictor slopes align with the signed moment discrepancies."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("contact-checker"), DeclarationHandle.Create(Prefix + "checkContactCertificate"), H("Finite rational checker"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance certificate", R(Check, Eq, Call("decide", Valid))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Decides all probability, moment, envelope, contact and alignment conditions from the raw data."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checker-reflection"), DeclarationHandle.Create(Prefix + "checkContactCertificate_eq_true_iff"), H("Acceptance reflection"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance certificate", R(R(Check, Eq, V("true")), Leftrightarrow, Valid)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance is equivalent to the displayed finite contract."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-attainment"), DeclarationHandle.Create(Prefix + "contact_gap_eq_budget"), H("Oriented gap attains the budget"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance certificate", R(Valid, Rightarrow,
                    R(R(Objective(CH), Minus, Objective(CL)), Eq, B(CE)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Contact and alignment make every contribution to the primal-dual gap vanish."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ambiguity-values"), DeclarationHandle.Create(Prefix + "ambiguityValues"), H("Attainable query differences"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance value", R(
                    R(V("value"), InMacro, Call("ambiguityValues", Feature, Query, Tol)), Leftrightarrow,
                    ExistsOver("high low", And(Pair(High, Low), R(V("value"), Eq, Abs(R(Objective(High), Minus, Objective(Low)))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both probability laws vary over the same finite carrier subject to the same tolerance vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-budget-values"), DeclarationHandle.Create(Prefix + "residualBudgetValues"), H("All valid residual budgets"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance value", R(
                    R(V("value"), InMacro, Call("residualBudgetValues", Feature, Query, Tol)), Leftrightarrow,
                    ExistsOver("envelope", And(Global(Env), R(V("value"), Eq, B(Env)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predictor and envelope may vary, while the carrier, query, features and tolerances stay fixed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-optimality"), DeclarationHandle.Create(Prefix + "checkContactCertificate_sound"), H("Attained maximum and attained minimum"),
                StatementSource.FromAuthor(Disp(All("n d feature query tolerance certificate", R(R(Check, Eq, V("true")), Rightarrow, And(
                    Call("IsGreatest", Call("ambiguityValues", Feature, Query, Tol), B(CE)),
                    Call("IsLeast", Call("residualBudgetValues", Feature, Query, Tol), B(CE))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same accepted value is the largest feasible query difference and the least valid residual budget. No general certificate-discovery or certificate-existence theorem is claimed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-compression"), DeclarationHandle.Create(Prefix + "contact_certificate_preserved_by_compression"), H("Sparse optimal witnesses without another query coordinate"),
                StatementSource.FromAuthor(Disp(CompressionFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("highSteps and lowSteps are lists of existing EliminationStep values. Separate support-monotone compression preserves the d feature moments, both residual contact levels and the signed alignment. Each endpoint has at most d+1 active atoms and the exact query gap is unchanged."))), DescribeRole.Theorem))));

    private static Formula GapFormula() => All("n d feature query tolerance high low envelope", R(
        And(R(S("i", Call("high", V("i"))), Eq, One), R(S("i", Call("low", V("i"))), Eq, One)), Rightarrow,
        R(R(B(Env), Minus, P(R(Objective(High), Minus, Objective(Low)))), Eq,
            R(R(S("i", R(P(R(Call("upper", Env), Minus, E(Env))), Cdot, Call("high", V("i")))), Plus,
                S("i", R(P(R(E(Env), Minus, Call("lower", Env))), Cdot, Call("low", V("i"))))), Plus,
                S("j", R(R(Abs(Coef(Env)), Cdot, Call("tolerance", V("j"))), Minus, R(Coef(Env), Cdot, P(DeltaMoment(High, Low)))))))));

    private static Formula CompressionFormula()
    {
        var updated = Seq(OpenBrace, R(V("high"), Eq, High), Comma, Sp,
            R(V("low"), Eq, Low), Comma, Sp, R(V("envelope"), Eq, CE), CloseBrace);
        return All("n d feature query tolerance certificate high low highSteps lowSteps", R(
            And(Valid, R(Call("checkCompression", Feature, CH, V("highSteps")), Eq, Call("some", High)),
                R(Call("checkCompression", Feature, CL, V("lowSteps")), Eq, Call("some", Low))), Rightarrow,
            And(Call("ValidContactCertificate", Feature, Query, Tol, updated),
                R(Call("card", Call("activeAtoms", High)), Le, R(V("d"), Plus, One)),
                R(Call("card", Call("activeAtoms", Low)), Le, R(V("d"), Plus, One)),
                R(R(Objective(High), Minus, Objective(Low)), Eq, R(Objective(CH), Minus, Objective(CL))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula R(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula Abs(Formula x) => Seq(Lvert, x, Rvert);
    private static Formula S(string index, Formula x) => Seq(Sum, Underscore, Grp(V(index)), Sp, P(x));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula ExistsOver(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula Quantify(Formula quantifier, string names, Formula body)
    {
        var items = new List<Formula> { quantifier, Sp };
        foreach (var name in names.Split(' ')) items.AddRange([V(name), Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var k = 0; k < clauses.Length; k++)
        {
            if (k > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[k]));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var k = 0; k < arguments.Length; k++)
        {
            if (k > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[k]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
