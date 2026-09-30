using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class CoPRelativeQuantumnessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/meunson2026cumulant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A completely positive, trace-preserving qubit channel that preserves commuting density matrices increases relative quantumness at alpha zero. The exact trace arguments of the logarithms are 50401283/7340144 before the channel and 1879639/266240 afterwards.",
        H("Relative quantumness can increase under a commutativity-preserving channel"),
        Blocks(
            Node("density", "Density matrices", DensityFormula(),
                "A density matrix on C^d is a positive semidefinite complex d by d matrix with trace one. PSD denotes Matrix.PosSemidef and Tr is the complex matrix trace.",
                "IsDensity", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reg", "Regularization", RegularizationFormula(),
                RegularizationQuote + " Here d is a natural number, A is a complex d by d matrix, and epsilon is real. The division epsilon/d is real division after casting d to the reals; I is the identity matrix and scalar multiplication is by a real scalar. The conjecture uses 0 < epsilon < 1.",
                "reg", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("q", "Relative quantumness at alpha zero", QFormula(),
                QuantumnessQuote + " The expression displayed here is literally minus S_0^Q, with the source factor 1/(0-1) and exponent (0-1)(log A-log B). Log of a matrix means continuous functional calculus for the real logarithm in the L2 operator norm; exp is the matrix exponential. The scalar logarithm is applied to the real part of the complex trace. On the positive definite matrices used below that trace is the positive real number calculated explicitly.",
                "Q", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cptp", "Completely positive trace-preserving maps", CPTPFormula(),
                "MatrixMap(Fin(d), Fin(d), C) is the type of complex-linear maps between d by d complex matrices. IsCompletelyPositive is the existing matrix-map predicate: every amplification by an identity map preserves positive semidefiniteness. Trace preservation is quantified over all complex matrices A, without a density-matrix restriction.",
                "IsCPTP", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cop", "Preservation of commuting density matrices", CoPFormula(),
                CoPQuote + " (Section VIII.A, PDF p. 18.) The predicate IsCoP encodes the commuting-pair condition; the separate IsCPTP premise supplies the CPTP requirement in the quoted definition. Equality AB = BA encodes the vanishing commutator. Both A and B range over all complex d by d matrices and are required to be density matrices.",
                "IsCoP", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("supp", "Matrix support", SupportFormula(),
                "The support of A is the range of the linear map Matrix.toLin' A on C^d, with the standard coordinate basis. For Hermitian positive semidefinite matrices this is the usual operator support. Inclusion of supports is the submodule order, written as subset inclusion.",
                "supp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 15", ClaimFormula(),
                ConjectureQuote + " (Conjecture 15, Section VIII.A, PDF p. 18.) Here H is C^d for arbitrary natural d; rho and sigma are density matrices; epsilon is real with 0 < epsilon < 1; and N is a complex-linear map satisfying IsCPTP and IsCoP. The source nonzero commutator is rho sigma and sigma rho differ. Rho_epsilon and sigma_epsilon are reg(epsilon,rho) and reg(epsilon,sigma). Support inclusion is inclusion of their output ranges. The two conclusion inequalities are encoded as Q(output rho,output sigma) <= Q(input rho,input sigma) and 0 <= Q(output rho,output sigma). The displayed pair normalizes the source typo.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A qubit refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Put t_n = (4^n-1)/(4^n+1), R = (I+t_7 Z)/2, S = (I+t_8 H)/2, R' = (I+t_6 Z)/2 and S' = (I+t_3 J)/2, where X and Z are Pauli matrices, H = (11 Z+5 sqrt(3) X)/14 and J = (29 Z+sqrt(455) X)/36. Set epsilon = 1/65537 and recover rho and sigma from R and S by undoing regularization. The unital channel has N(X) = u X+v Z, N(Y) = u w Y and N(Z) = w Z, with u = (3211313/127793250) sqrt(1365), v = -(727356123473/168188824118250) sqrt(3), w = 22365525/22373717. Four explicit Kraus operators realize the channel: reshape the vectors bp(v/a), ep, bm(v/b), em in output-input index order and scale them by sqrt(a/4), sqrt(delta/(4a)), sqrt(b/4), sqrt(delta/(4b)), where a=(1+u)(1+w), b=(1-u)(1+w) and delta=(1-u^2)(1-w^2)-v^2. Entrywise equality to the Kraus sum proves complete positivity using the frozen Kraus-channel theorem; its trace is preserved on every input. Entrywise commutator identities show preservation of every commuting pair. The inputs are noncommuting density matrices, and both outputs are positive definite, so the support inclusion holds. Two-point functional calculus for self-adjoint involutions gives Tr[R exp(log S-log R)] = 50401283/7340144 < 1879639/266240 = Tr[R' exp(log S'-log R')]. Strict monotonicity of the real logarithm contradicts the first inequality of Conjecture 15.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private const string RegularizationQuote = """
        Given $\rho,\sigma\in\mathcal D(\mathcal H)$ and a parameter $\varepsilon\in(0,1)$, define $\rho_\varepsilon := (1-\varepsilon)\rho + \varepsilon\frac{\mathbb{I}}{d}, \quad \sigma_\varepsilon := (1-\varepsilon)\sigma + \varepsilon\frac{\mathbb{I}}{d}$, where $d=\dim(\mathcal H)$.
        """;
    private const string QuantumnessQuote = """
        Define $Q(\rho_\varepsilon\|\sigma_\varepsilon) := -S_0^Q(\rho_\varepsilon\|\sigma_\varepsilon)$.
        """;
    private const string CoPQuote = """
        Let $\mathcal{H}$ be a finite-dimensional Hilbert space. A CPTP map $\mathcal{N}:\mathcal{B}(\mathcal{H})\to\mathcal{B}(\mathcal{H})$ is called a CoP channel if, for every pair $(\rho,\sigma)\in\mathcal{D}(\mathcal{H})\times \mathcal{D}(\mathcal{H})$ satisfying $[\rho,\sigma]=0$, one has $[\mathcal {N}(\rho),\mathcal {N}(\sigma)]=0$.
        """;
    private const string ConjectureQuote = """
        \begin{conjecture}[QDPI at $\alpha=0$ for non-commuting inputs under CoP channels] Let $\rho,\sigma)\in \mathcal D(\mathcal H)\times\mathcal D(\mathcal H)$ satisfy $[\rho,\sigma]\neq0,$ where $\rho_\varepsilon,\sigma_\varepsilon$ are the regularized states defined in Eq.\eqref{state_regularized}. Suppose that $\mathcal N $ is a CoP channel satisfying $\operatorname{supp}\!\bigl(\mathcal N(\rho_\varepsilon)\bigr) \subseteq\operatorname{supp}\!\bigl(\mathcal N(\sigma_\varepsilon)\bigr). $ Then, \begin{equation} Q(\rho_\varepsilon\|\sigma_\varepsilon) \geq Q\left( \mathcal N(\rho_\varepsilon)\|\, \mathcal N(\sigma_\varepsilon) \right) \geq 0. \end{equation} \end{conjecture}
        """;

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("copquantumness-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(declaration == "claim"
                ? [.. SourceInline(prose), Text(@" Verbatim malformed source fragment: \rho,\sigma)\in \mathcal D(\mathcal H)\times\mathcal D(\mathcal H).")]
                : SourceInline(prose))), role);

    private static Inline[] SourceInline(string prose)
    {
        var parts = prose.Split('$');
        var output = new System.Collections.Generic.List<Inline>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (parts[i].Length == 0) continue;
            if (i % 2 == 1)
            {
                output.Add(Math(SourceMath(parts[i])));
                continue;
            }
            const string start = "\\begin{equation} ";
            const string end = " \\end{equation}";
            var from = parts[i].IndexOf(start, System.StringComparison.Ordinal);
            if (from < 0)
            {
                output.Add(Text(parts[i]));
                continue;
            }
            var to = parts[i].IndexOf(end, from, System.StringComparison.Ordinal);
            output.Add(Text(parts[i][..(from + start.Length)]));
            output.Add(Math(SourceConclusion()));
            output.Add(Text(parts[i][to..]));
        }
        return [.. output];
    }

    private static Formula Cal(string letter) => Seq(Mathcal, Grp(F.Id(letter)));
    private static Formula SourceApply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Indexed(Formula f) => Seq(f, Underscore, Grp(Varepsilon));
    private static Formula Commutator(Formula a, Formula b) => Seq(
        new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), a, Comma, b,
        new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket));
    private static Formula PaperQ(Formula a, Formula b) =>
        SourceApply(F.Id("Q"), Seq(a, Vert, b));
    private static Formula SourceConclusion()
    {
        Formula r = Indexed(Rho), s = Indexed(SigmaLower);
        return Seq(PaperQ(r, s), Geq, Sp,
            PaperQ(SourceApply(Cal("N"), r), SourceApply(Cal("N"), s)), Geq, Sp, D(0),
            new Formula.LatexSymbol(FormulaLatexSymbol.Period));
    }

    private static Formula SourceMath(string text)
    {
        // The fragment order below is the order of the source's math runs, not a parser.
        string[] math = [.. RegularizationQuote.Split('$').Where((_, i) => i % 2 == 1),
            .. QuantumnessQuote.Split('$').Where((_, i) => i % 2 == 1),
            .. CoPQuote.Split('$').Where((_, i) => i % 2 == 1),
            .. ConjectureQuote.Split('$').Where((_, i) => i % 2 == 1)];
        var index = System.Array.IndexOf(math, text);
        Formula h = Cal("H"), n = Cal("N"), density = SourceApply(Cal("D"), h);
        Formula pair = Parenthesized(Seq(Rho, Comma, SigmaLower));
        Formula r = Indexed(Rho), s = Indexed(SigmaLower);
        Formula nr = SourceApply(n, r), ns = SourceApply(n, s);
        Formula comm = Commutator(Rho, SigmaLower);
        Formula sourceReg = Seq(Parenthesized(MinusOf(D(1), Varepsilon)), Rho, Plus,
            Varepsilon, new Formula.Fraction(Seq(Mathbb, Grp(F.Id("I"))), F.Id("d")));
        Formula sourceRegSigma = Seq(Parenthesized(MinusOf(D(1), Varepsilon)), SigmaLower, Plus,
            Varepsilon, new Formula.Fraction(Seq(Mathbb, Grp(F.Id("I"))), F.Id("d")));
        return index switch
        {
            0 => Seq(Rho, Comma, SigmaLower, InMacro, density),
            1 => Seq(Varepsilon, InMacro, Parenthesized(Seq(D(0), Comma, D(1)))),
            2 => Seq(r, Colon, Eq, sourceReg, Comma, Quad, s, Colon, Eq, sourceRegSigma),
            3 => Equal(F.Id("d"), Call("dim", h)),
            4 => Seq(PaperQ(r, s), Colon, Eq, Minus, SourceApply(
                Seq(F.Id("S"), Underscore, Grp(D(0)), Caret, Grp(F.Id("Q"))), Seq(r, Vert, s))),
            5 => h,
            6 => Seq(n, Colon, SourceApply(Cal("B"), h), To, SourceApply(Cal("B"), h)),
            7 => Seq(pair, InMacro, density, F.Times, density),
            8 => Equal(comm, D(0)),
            9 => Equal(Commutator(SourceApply(n, Rho), SourceApply(n, SigmaLower)), D(0)),
            10 => Equal(Alpha, D(0)),
            11 => Seq(Parenthesized(Seq(Rho, Comma, SigmaLower)), InMacro, density, F.Times, density),
            12 => Seq(new Formula.Relation(comm, FormulaRelationOperator.NotEqual, D(0)), Comma),
            13 => Seq(r, Comma, s),
            14 => n,
            15 => Seq(new Formula.Relation(Call("supp", nr), FormulaRelationOperator.SubsetOf,
                Call("supp", ns)), new Formula.LatexSymbol(FormulaLatexSymbol.Period), Sp),
            _ => throw new System.ArgumentException("Unrecognized source math run.", nameof(text)),
        };
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
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
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MinusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Scalar(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(Formula d) => Seq(Complexes(), Caret, Grp(d, F.Times, Sp, d));
    private static Formula Map(Formula d) => Call("MatrixMap", Call("Fin", d), Call("Fin", d), Complexes());
    private static Formula Apply(Formula n, Formula a) => new Formula.Apply(n, [a]);
    private static Formula Density(Formula a) => Call("IsDensity", a);
    private static Formula Reg(Formula epsilon, Formula a) => Call("reg", epsilon, a);
    private static Formula Quantumness(Formula a, Formula b) => Call("Q", a, b);

    private static Formula DensityFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A");
        return Disp(All(d, Naturals(), All(a, Mat(d),
            Iff(Density(a), And(Call("PSD", a), Equal(Call("Tr", a), D(1)))))));
    }

    private static Formula RegularizationFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A"), epsilon = Varepsilon;
        Formula scalar = Parenthesized(MinusOf(D(1), epsilon));
        Formula cast = Call("real", d);
        Formula body = new Formula.Binary(Scalar(scalar, a), FormulaBinaryOperator.Add,
            Scalar(new Formula.Fraction(epsilon, cast), F.Id("I")));
        return Disp(All(d, Naturals(), All(epsilon, Reals(), All(a, Mat(d), Equal(Reg(epsilon, a), body)))));
    }

    private static Formula QFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A"), b = F.Id("B");
        Formula zeroMinusOne = Parenthesized(MinusOf(D(0), D(1)));
        Formula delta = Parenthesized(MinusOf(Call("log", a), Call("log", b)));
        Formula exponent = Scalar(zeroMinusOne, delta);
        Formula trace = Call("Re", Call("Tr", TimesOf(a, Call("exp", exponent))));
        Formula value = new Formula.Negate(Parenthesized(TimesOf(
            new Formula.Fraction(D(1), zeroMinusOne), Call("ln", trace))));
        return Disp(All(d, Naturals(), All(a, Mat(d), All(b, Mat(d), Equal(Quantumness(a, b), value)))));
    }

    private static Formula CPTPFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), a = F.Id("A");
        Formula tp = All(a, Mat(d), Equal(Call("Tr", Apply(n, a)), Call("Tr", a)));
        return Disp(All(d, Naturals(), All(n, Map(d),
            Iff(Call("IsCPTP", n), And(Call("IsCompletelyPositive", n), tp)))));
    }

    private static Formula CoPFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), a = F.Id("A"), b = F.Id("B");
        Formula commute = Equal(TimesOf(a, b), TimesOf(b, a));
        Formula na = Apply(n, a), nb = Apply(n, b);
        Formula output = Equal(TimesOf(na, nb), TimesOf(nb, na));
        Formula body = All(a, Mat(d), All(b, Mat(d),
            Implies(Density(a), Implies(Density(b), Implies(commute, output)))));
        return Disp(All(d, Naturals(), All(n, Map(d), Iff(Call("IsCoP", n), body))));
    }

    private static Formula SupportFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A");
        Formula toLin = new Formula.Apply(
            Seq(Named("toLin"), new Formula.LatexSymbol(FormulaLatexSymbol.Apostrophe)), [a]);
        return Disp(All(d, Naturals(), All(a, Mat(d), Equal(Call("supp", a), Call("range", toLin)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), rho = Rho, sigma = SigmaLower, epsilon = Varepsilon, n = F.Id("N");
        Formula r = Reg(epsilon, rho), s = Reg(epsilon, sigma), nr = Apply(n, r), ns = Apply(n, s);
        Formula noncommuting = new Formula.Relation(TimesOf(rho, sigma), FormulaRelationOperator.NotEqual, TimesOf(sigma, rho));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, epsilon);
        Formula belowOne = new Formula.Relation(epsilon, FormulaRelationOperator.LessThan, D(1));
        Formula supports = new Formula.Relation(Call("supp", nr), FormulaRelationOperator.SubsetOf, Call("supp", ns));
        Formula output = And(Leq(Quantumness(nr, ns), Quantumness(r, s)), Leq(D(0), Quantumness(nr, ns)));
        Formula body = Implies(Density(rho), Implies(Density(sigma), Implies(noncommuting,
            Implies(positive, Implies(belowOne, Implies(Call("IsCPTP", n), Implies(Call("IsCoP", n), Implies(supports, output))))))));
        return Disp(Iff(F.Id("claim"), All(d, Naturals(), All(rho, Mat(d), All(sigma, Mat(d),
            All(epsilon, Reals(), All(n, Map(d), body)))))));
    }
}
