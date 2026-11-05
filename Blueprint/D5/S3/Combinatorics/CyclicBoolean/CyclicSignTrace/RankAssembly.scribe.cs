using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace;

internal sealed class CyclicSignTraceRankAssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/Fourier/ricardorr2026mo512655");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic overlap constraints bound the constant-derivative space and assemble the complete odd-length affine-support theorem.",
        H("Rank assembly for the odd cyclic trace support"),
        Blocks(
            Paragraph(Text("For positive m, each topVariables(m,i) has exactly one adjacent cyclic pair, at i+2m-1 and i+2m. The prefix itself contains no adjacent pair, including across the cyclic boundary. Deleting any other coordinate a leaves this pair intact, so any top variable set containing the deletion must have the same index i. Applying the degree-m derivative equation at that deletion therefore proves b_i u_a=0. This establishes the interior-deletion constraints for every odd length at least five, and the same implication at length three where there is no interior coordinate. An endpoint deletion is a full prefix. A prefix has no adjacent pair, so an equal-cardinality prefix contained in a top set must be obtained by deleting one of its adjacent pair. The two possible top indices are i and i+2, and coefficient extraction gives b_i u_(i-1)=b_(i+2) u_i at every positive m.")),
            Paragraph(Text("For m≥2 and an active mask bit, the interior constraints fix every prefix of length less than m under translation by u. Differentiating the shifted inverse expression leaves two degree-m sums, which cancel by the endpoint equation after a cyclic reindexing. The remaining expression is the sum over i and r<m of b_i u_(i+2r) P_(i,r), plus the sum over i of b_i u_(i-2)(1+u_(i-1)) P_(i,m-1). Every proper nonempty step-two prefix has a unique start: its first coordinate is present and its predecessor by two is absent. Prefix cardinalities separate different lengths. Extracting these actual Boolean function coefficients gives (A): b_i u_(i+r)=0 for 1≤r≤2m-3, and (C): b_i[u_(i-3)+u_(i-2)(1+u_(i-1))]=0. Empty earlier ranges at m=2 are preserved.")),
            Paragraph(Text("For m≥2, a nonzero mask is either all-one or has a coordinate i with b_i=1 and b_(i-2)=0. The latter alternative follows by propagating active bits backwards by two around the odd cycle if no such boundary exists. The all-one mask makes every derivative direction zero by (A). At a boundary, (B) gives u_(i-2)=0, then (C) gives u_(i-3)=0, while u_(i-1)=b_(i+2) u_i. Equation (A) kills every remaining coordinate. Thus evaluation at i is an injective linear map from the derivative subspace into ZMod 2, proving dimension at most one. This argument covers length five directly and requires no orientation-uniqueness assumption.")),
            Paragraph(Text("At length three, choose any active mask coordinate i. The same endpoint equation determines both other direction coordinates from u_i, so coordinate evaluation is again injective. Length one has the required lower bound zero. For every other odd length, combine the derivative-space dimension bound with constantDerivative_affineSpan_duality and the dimension 2m+1 of the full binary word space. The exact sourceTrace_eq_phase_sum and inverse_phase_sum identities identify the literal trace support with the inverse-component Walsh support, giving the original affine-dimension inequality.")),
            Describe.Lean(DescribeId.Create("cyclic-sign-trace-affine-trace-support-dimension"),
                DeclarationHandle.Create(Prefix + "affine_trace_support_dimension"),
                H("The complete odd-length trace-support bound"),
                StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.SupportDimensionFormula()),
                AssessedProvenance.FromRepo(SourceNote),
                Blocks(
                    Paragraph(Text("For every natural m and every nonzero binary word b of length 2m+1, the affine span over ZMod 2 of all a with nonzero literal ordered integer sourceTrace(b,a) has direction dimension at least 2m. All positive odd lengths, including one and three, and every nonzero mask are retained. The proof assumes neither the direction classification nor a coefficient-uniqueness or dimension conclusion. This is the complete assertion defined by claim."))
                ), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-512655-cyclic-sign-trace-affine-support"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The literal trace model follows ricardorr, MathOverflow question 512655, original revision E06A6743-2C15-41CD-9390-04D1862ABA02, https://mathoverflow.net/questions/512655, attributed under CC-BY-SA 4.0. The inverse argument above is a direct derivation for this cyclic map.")),
            Paragraph(Text("The theorem establishes the full mathematical inequality for the specified model. It does not assert that every support is a hyperplane or classify all masks attaining equality. The source attribution and library reuse do not establish a novelty or priority claim."))
        ), []));
}

internal static class CyclicSignTraceScribeFormulas
{
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Some(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(Grp(a), op, Grp(b));
    private static Formula Plus(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Times(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Word(Formula n) => Call("Word", n);
    private static Formula Sum(string x, Formula t, Formula body) => Seq(F.Sum, Underscore, Grp(F.Id(x), Sp, InMacro, Sp, t), Sp, body);
    private static Formula OddLength(Formula m) => Plus(Times(D(2), m), D(1));

    internal static Formula InverseFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"),
            And(All("x", w, Eq(Call("inverse", m, Call("chi", x)), x)),
                All("y", w, Eq(Call("chi", Call("inverse", m, y)), y)))));
    }

    internal static Formula InversionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), y = F.Id("y"), a = F.Id("a"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), All("y", w,
                Eq(Sum("a", w, Times(Call("walsh", f, a), Call("sign", Call("dot", a, y)))),
                    Times(Call("card", w), Call("sign", Call("f", y)))))))));
    }

    internal static Formula NonemptyFormula()
    {
        Formula n = F.Id("n"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), Some("a", w,
                Rel(Call("walsh", F.Id("f"), F.Id("a")), FormulaRelationOperator.NotEqual, D(0)))))));
    }

    internal static Formula PhaseNonemptyFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, Some("a", w,
            Rel(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                FormulaRelationOperator.NotEqual, D(0))))));
    }

    internal static Formula PhaseFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, All("a", w,
            Eq(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                Call("walsh", Call("inverseComponent", m, b), a))))));
    }

    internal static Formula WalshDerivativeFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"),
            y = F.Id("y"), a = F.Id("a"), w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = All("y", w,
            Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c));
        Formula support = All("a", w,
            Imp(new Formula.Relation(Call("walsh", f, a), FormulaRelationOperator.NotEqual, D(0)),
                Eq(Call("dot", a, u), c)));
        return Disp(All("n", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
                All("f", Arrow(w, bit), All("u", w, All("c", bit,
                    new Formula.Logic(Grp(derivative), FormulaLogicOperator.Iff,
                        Grp(support))))))));
    }

    internal static Formula AffineDualityFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"), y = F.Id("y"),
            w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = Some("c", bit,
            All("y", w, Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c)));
        Formula membership = Call("mem", u, Call("constantDerivativeSubmodule", f));
        Formula finrankD = Call("finrank", bit, Call("constantDerivativeSubmodule", f));
        Formula finrankA = Call("finrank", bit, Call("walshSupportDirection", f));
        Formula finrankV = Call("finrank", bit, w);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, bit),
                And(All("u", w,
                        new Formula.Logic(Grp(membership), FormulaLogicOperator.Iff,
                            Grp(derivative))),
                    Eq(Plus(finrankD, finrankA), finrankV))))));
    }

    internal static Formula TracePhaseFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("b", w, All("a", w,
                Eq(Call("sourceTrace", b, a),
                    Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x)))))))))));
    }

    internal static Formula BooleanCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), s = F.Id("s"), i = F.Id("i"), r = F.Id("r"),
            n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula delta(Formula t) => Call("ite", Eq(s, t), D(1), D(0));
        Formula endpoint = Plus(i, Times(D(2), r));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(delta(p), delta(Call("insert", endpoint, p))))));
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n),
            All("s", Call("Finset", Call("ZMod", n)), Eq(Call("booleanCoeff", shifted, s), rhs)))));
    }

    internal static Formula DerivativeCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), r = F.Id("r"), y = F.Id("y"), n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula constant = Some("c", Call("ZMod", D(2)), All("y", Word(n),
            Eq(Plus(Call("inverseComponent", m, b, Plus(y, u)), Call("inverseComponent", m, b, y)), F.Id("c"))));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(Call("monomialDerivativeCoeff", p, s, u),
                Call("monomialDerivativeCoeff", Call("insert", Plus(i, Times(D(2), r)), p), s, u)))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("u", Word(n),
            Imp(constant, All("s", Call("Finset", Call("ZMod", n)),
                Imp(Call("Nonempty", s), Eq(rhs, D(0)))))))));
    }

    internal static Formula TopCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), i = F.Id("i"), n = OddLength(m);
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("i", Call("ZMod", n),
            Eq(Call("booleanCoeff", shifted, Call("topVariables", m, i)), Call("b", i))))));
    }

    internal static Formula TopDerivativeFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), n = OddLength(m), t = Call("topVariables", m, i);
        Formula summand = Times(Call("b", i), Call("ite", Call("subset", s, t),
            Call("booleanMonomial", Call("sdiff", t, s), u), D(0)));
        Formula sets = All("s", Call("Finset", Call("ZMod", n)),
            Imp(Eq(Call("card", s), m), Eq(Sum("i", Call("ZMod", n), summand), D(0))));
        Formula directions = All("b", Word(n), All("u", Word(n), Imp(
            Call("mem", u, Call("constantDerivativeSubmodule", Call("inverseComponent", m, b))), sets)));
        return Disp(All("m", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, m), directions)));
    }

    internal static Formula SupportDimensionFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), n = OddLength(m), bit = Call("ZMod", D(2));
        Formula rank = Call("finrank", bit, Call("direction", Call("affineSpan", bit, Call("traceSupport", b))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), Imp(
            Rel(b, FormulaRelationOperator.NotEqual, D(0)),
            Rel(Times(D(2), m), FormulaRelationOperator.LessThanOrEqual, rank)))));
    }
}
