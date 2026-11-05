using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class SicMubCorrelationTraceNormEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/tavakolimorelli2024schmidttracenorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SIC and complete-MUB correlation matrices have proportional rectangular trace norms.",
        H("SIC–MUB correlation trace-norm equality"),
        Blocks(
            Paragraph(Text(
                "All vector and matrix entries are complex. Natural dimensions are used as finite index sizes, "
                    + "and FiniteTraceDistance.traceNorm is the real part of the trace of the positive square root "
                    + "of the matrix's conjugate transpose times the matrix. "
                    + "MUBFamily and its effect are those of TavakoliMorelliIncompleteMUB: "
                    + "a complete family has d + 1 unitary bases, with squared overlaps 1/(d : ℝ) between distinct bases. "
                    + "Its effect at a pair p is the rank-one projector onto column p.2 of basis p.1.")),
            Node("SICFamily", "SIC families", SICFamilyFormula(),
                "A SIC family consists of d squared vectors in C to the d, each of unit norm, with squared modulus overlap 1/(d+1) for every distinct pair. The subtype retains exactly these normalization and equiangularity conditions.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sicEffect", "SIC effects", SicEffectFormula(),
                "The effect indexed by i is the rank-one projector of the i-th SIC vector scaled by the inverse of d.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sicCorrelation", "The SIC correlation matrix", SicCorrelationFormula(),
                "For a bipartite operator and two local SIC families, the rectangular matrix records the trace of the operator against every tensor product of local SIC effects. Its row and column sets have sizes d_A squared and d_B squared.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mubCorrelation", "The complete-MUB correlation matrix", MubCorrelationFormula(),
                "For two complete MUB families, the rectangular matrix records the trace against every pair of rank-one MUB effects. Its row and column labels are basis and outcome pairs.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The SIC–MUB trace-norm equality", ClaimFormula(),
                "Conjecture 1 states that for local dimensions at least two, every pair of SIC families, every pair of complete MUB families, and every positive semidefinite trace-one bipartite operator, the complete-MUB trace norm equals the SIC trace norm multiplied by the two dimension factors.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("sic-mub-correlation-trace-norm-trace-pairing-ext"),
                DeclarationHandle.Create(Prefix + "trace_pairing_ext"),
                H("Trace pairings on a spanning family"),
                StatementSource.FromAuthor(TracePairingExtFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Two complex square matrices are equal when their trace pairings agree on a family whose complex linear span is the full matrix space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sic-mub-correlation-trace-norm-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The equality follows from two frames and an isometry"),
                StatementSource.FromAuthor(Disp(X("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a local dimension d at least two, a SIC family S, and any complex d by d matrix X, sic_frame reconstructs X from its traces against sicEffect S i. The identity sicProjector_sum says that the sum of rankOneDensity(S.val i) over all i in Fin (d * d) is (d : ℂ) times the identity. For a complete MUB family M, mub_frame says that the sum of trace(M.effect p * X) times M.effect p over p in Fin (d + 1) times Fin d is X plus trace(X) times the identity.")),
                    Paragraph(Text(
                        "For a local dimension d at least two, a SIC family S, and a complete MUB family M, transition S M has row indices p in Fin (d + 1) times Fin d and column indices i in Fin (d * d). Its (p, i) entry is ((d : ℂ) + 1) times trace(rankOneDensity(S.val i) * M.effect p), minus one. The entries are real by transition_real, and transition_gram says that its conjugate transpose times itself is (d : ℂ) * ((d : ℂ) + 1) times the identity.")),
                    Paragraph(Text(
                        "For the dimensions, families, and operator in claim, correlation_transition expresses mubCorrelation rho MA MB as transition SA MA times sicCorrelation rho SA SB times the conjugate transpose of transition SB MB. For each local dimension d, the transition matrix is the square root of (d : ℝ) * ((d : ℝ) + 1) times an isometry. The theorem scaled_isometry_traceNorm uses uniqueness of the positive square root and cyclicity of the trace to give the stated product of square-root factors."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tavakoli-morelli-2024-conjecture-1-sic-mub-trace-norm-equality"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("sic-mub-correlation-trace-norm-" + name.Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Cast(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Arrow(Formula left, Formula right) =>
        Parenthesized(new Formula.TypeArrow(left, right));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        At(X(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Field(Formula value, string name) =>
        Seq(Parenthesized(value), Dot, X(name));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) => Call("Matrix", rows, cols, Complex());
    private static Formula MatrixPair(Formula left, Formula right) => Matrix(Pair(left, right), Pair(left, right));
    private static Formula Vec(Formula d) => Arrow(Fin(d), Complex());
    private static Formula SIC(Formula d) => Call("SICFamily", d);
    private static Formula MUB(Formula d) => Call("MUBFamily", d, Add(d, D(1)));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Cast(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula SetSubtype(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Cast(X(name), type), Sp, Slash, Sp, Slash, Sp, body, CloseBrace);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Scale(Formula scalar, Formula value) => Call("smul", scalar, value);
    private static Formula Star(Formula value) => Call("star", value);
    private static Formula DotProduct(Formula left, Formula right) => Call("dotProduct", left, right);
    private static Formula Outer(Formula value) => Call("rankOneDensity", value);
    private static Formula Tensor(Formula left, Formula right) => Call("kronecker", left, right);
    private static Formula Trace(Formula value) => Call("trace", value);
    private static Formula Of(Formula rows, Formula cols, Formula body) =>
        At(Qualified("Matrix", "of"), Lambda("i", rows, Lambda("j", cols, body)));

    private static Formula TracePairingExtFormula()
    {
        Formula d = X("d"), iota = Iota, p = X("P"), x = X("X"), y = X("Y");
        Formula matrix = Matrix(Fin(d), Fin(d));
        Formula spanning = Equal(At(Qualified("Submodule", "span"), Complex(),
            At(Qualified("Set", "range"), p)), Qualified("Top", "top"));
        Formula pairings = All("i", iota,
            Equal(Trace(Multiply(x, At(p, X("i")))), Trace(Multiply(y, At(p, X("i"))))));
        return Disp(All("d", Nat(), Seq(Forall, Sp, Cast(iota, X("Type")), Comma, Sp,
            Parenthesized(All("P", Arrow(iota, matrix),
                Implication(spanning, All("X", matrix, All("Y", matrix,
                    Implication(pairings, Equal(x, y))))))))));
    }

    private static Formula SICFamilyFormula()
    {
        Formula d = X("d"), i = X("i"), j = X("j"), psi = X("psi");
        Formula vectorType = Arrow(Fin(Multiply(d, d)), Vec(d));
        Formula unit = All("i", Fin(Multiply(d, d)),
            Equal(DotProduct(Star(At(psi, i)), At(psi, i)), D(1)));
        Formula overlap = Equal(Power(Norm(DotProduct(Star(At(psi, i)), At(psi, j))), D(2)),
            Fraction(D(1), Add(Cast(d, Real()), D(1))));
        Formula distinct = All("i", Fin(Multiply(d, d)), All("j", Fin(Multiply(d, d)),
            Implication(NotEqual(i, j), overlap)));
        return Disp(All("d", Nat(), Equal(SIC(d), SetSubtype("psi", vectorType, And(unit, distinct)))));
    }

    private static Formula SicEffectFormula()
    {
        Formula d = X("d"), s = X("S"), i = X("i");
        Formula scalar = Fraction(D(1), Cast(d, Complex()));
        return Disp(All("d", Nat(), All("S", SIC(d), All("i", Fin(Multiply(d, d)),
            Equal(Call("sicEffect", s, i), Scale(scalar, Outer(At(Call("val", s), i))))))));
    }

    private static Formula SicCorrelationFormula()
    {
        Formula dA = X("dA"), dB = X("dB"), rho = X("rho"), sa = X("SA"), sb = X("SB");
        Formula row = Fin(Multiply(dA, dA)), col = Fin(Multiply(dB, dB));
        Formula body = Trace(Multiply(rho, Tensor(
            Call("sicEffect", sa, X("i")), Call("sicEffect", sb, X("j")))));
        return Disp(All("dA", Nat(), All("dB", Nat(),
            All("rho", MatrixPair(Fin(dA), Fin(dB)),
                All("SA", SIC(dA), All("SB", SIC(dB),
                    Equal(Call("sicCorrelation", rho, sa, sb), Of(row, col, body))))))));
    }

    private static Formula MubCorrelationFormula()
    {
        Formula dA = X("dA"), dB = X("dB"), rho = X("rho"), ma = X("MA"), mb = X("MB");
        Formula row = Pair(Fin(Add(dA, D(1))), Fin(dA));
        Formula col = Pair(Fin(Add(dB, D(1))), Fin(dB));
        Formula body = Trace(Multiply(rho, Tensor(
            At(Field(ma, "effect"), X("i")), At(Field(mb, "effect"), X("j")))));
        return Disp(All("dA", Nat(), All("dB", Nat(),
            All("rho", MatrixPair(Fin(dA), Fin(dB)),
                All("MA", MUB(dA), All("MB", MUB(dB),
                    Equal(Call("mubCorrelation", rho, ma, mb), Of(row, col, body))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula dA = X("dA"), dB = X("dB"), rho = X("rho"), sa = X("SA"), sb = X("SB"), ma = X("MA"), mb = X("MB");
        Formula state = MatrixPair(Fin(dA), Fin(dB));
        Formula factorA = At(Qualified("Real", "sqrt"), Multiply(Cast(dA, Real()), Add(Cast(dA, Real()), D(1))));
        Formula factorB = At(Qualified("Real", "sqrt"), Multiply(Cast(dB, Real()), Add(Cast(dB, Real()), D(1))));
        Formula equality = Equal(Call("traceNorm", Call("mubCorrelation", rho, ma, mb)),
            Multiply(Multiply(factorA, factorB), Call("traceNorm", Call("sicCorrelation", rho, sa, sb))));
        Formula stateHypothesis = Implication(Call("PosSemidef", rho),
            Implication(Equal(Trace(rho), D(1)), equality));
        Formula quantified = All("rho", state, stateHypothesis);
        Formula families = All("SA", SIC(dA), All("SB", SIC(dB),
            All("MA", MUB(dA), All("MB", MUB(dB), quantified))));
        Formula hypotheses = Implication(LE(D(2), dA), Implication(LE(D(2), dB), families));
        return Disp(All("dA", Nat(), All("dB", Nat(), hypotheses)));
    }
}
