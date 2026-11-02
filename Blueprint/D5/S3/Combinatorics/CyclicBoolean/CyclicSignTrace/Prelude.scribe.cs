using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace;

internal sealed class CyclicSignTracePreludeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/Fourier/ricardorr2026mo512655");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The foundational odd-cycle inverse, Walsh bridge, and affine duality for the cyclic Boolean sign-trace model.",
        H("Cyclic Boolean foundations"),
        Blocks(
            Node("Word", "Binary words on a cyclic index set", StatementSource.WithoutFormula(),
                "A word of length n is a function from ZMod n to the binary field ZMod 2. All additions in an index are modulo n; all additions in a word value are modulo two.", DescribeRole.Definition),
            Node("chi", "The forward cyclic map", StatementSource.WithoutFormula(),
                "At index i, chi(x) is x_i + x_(i+2) + x_(i+1) x_(i+2). Repeated indices denote the same variable, including at length one.", DescribeRole.Definition),
            Node("sign", "Integer signs", StatementSource.WithoutFormula(),
                "The sign of a binary field element z is the integer (-1) raised to its representative z.val, which is zero or one.", DescribeRole.Definition),
            Node("sourceMatrix", "The literal source matrix", StatementSource.WithoutFormula(),
                "For arbitrary binary words b and a and cyclic index k, the entry at binary row s and column t is sign((a_k + a_(k-2) + b_k)s + a_(k-1)st). The first row is (1,1); the second is ((-1)^h_k,(-1)^(h_k+g_k)), with g_k=a_(k-1) and h_k=a_k+a_(k-2)+b_k.", DescribeRole.Definition),
            Node("sourceTrace", "The ordered integer trace", StatementSource.WithoutFormula(),
                "Form the list of source matrices at representatives zero through n-1 in that order, multiply the list, and take its integer matrix trace. No commutation of matrix factors is used.", DescribeRole.Definition),
            Node("traceSupport", "Nonzero trace support", StatementSource.WithoutFormula(),
                "The trace support consists of every a for which the literal ordered integer trace is nonzero. No word a is excluded.", DescribeRole.Definition),
            Node("claim", "The full affine-support question", StatementSource.WithoutFormula(),
                "For every natural m and every nonzero b of length 2m+1, the direction of the affine span over ZMod 2 of the trace support has dimension at least 2m. The parameter m runs from zero, so this is exactly all positive odd lengths, including length one. The inequality is a lower bound, not an equality. The final theorem proves this assertion through the exact trace and Walsh identities and a bound on constant-derivative directions.", DescribeRole.Definition),
            Node("alternatingPrefix", "Alternating products", StatementSource.WithoutFormula(),
                "The alternating prefix at i of length t is the product, for r from zero through t-1, of 1+y_(i+2r+1). The empty product is one.", DescribeRole.Definition),
            Node("inverse", "The inverse polynomial", StatementSource.WithoutFormula(),
                "At length 2m+1, the inverse coordinate at i is the sum, for r from zero through m, of y_(i+2r) times the alternating prefix at i of length r. Thus its first term is y_i.", DescribeRole.Definition),
            Node("inverse_spec", "Both inverse identities at every positive odd length", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.InverseFormula()),
                "For every m, applying the inverse polynomial after chi gives the original word, and applying chi after the inverse polynomial does the same. The proof does not assume either identity or invertibility.", DescribeRole.Theorem),
            Node("twice_half", "Two has an inverse on the odd cycle", StatementSource.WithoutFormula(),
                "Multiplication by two and the displayed half-index construction are inverse on ZMod (2*m+1). This helper supplies the actual odd-cycle reindexing used by the inverse proof.", DescribeRole.Lemma),
            Node("step_two_reaches", "Step-two traversal reaches every odd-cycle index", StatementSource.WithoutFormula(),
                "For every odd cycle, repeated addition of two reaches any target index from any start. The result is used to propagate the inverse recurrence around the complete cycle.", DescribeRole.Lemma),
            Paragraph(Text("Write y=chi(x). The local Boolean identity is x_i=y_i+(1+y_(i+1))x_(i+2). Iterating t times gives the first t terms of the inverse polynomial plus the alternating prefix of length t times x_(i+2t). For t=m+1 the latter x-coordinate is x_(i+1). If this tail were nonzero, x_(i+1) would be one and the m+1 alternating y-coordinates would all vanish. At each of these positions the recurrence forces the next intervening y-coordinate to vanish and the next x-coordinate in steps of two to be one. The even and odd representatives together cover the cycle, hence y=0.")),
            Paragraph(Text("When chi(x)=0 the recurrence makes x invariant under addition of two. Multiplication by m+1 is an inverse to multiplication by two modulo 2m+1, so every index is reached and x is constant. The image under chi of a constant binary word is that same constant word. Thus the zero fiber contains only the zero word, contradicting the tail's x-coordinate being one. This proves the left inverse identity. The finite domain and codomain have the same cardinality, so injectivity gives surjectivity and hence the right inverse identity.")),
            Node("dot", "Binary dot products", StatementSource.WithoutFormula(),
                "The dot product of a and x is the sum over all cyclic indices of a_i x_i in ZMod 2.", DescribeRole.Definition),
            Node("walsh", "Unnormalized integer Walsh coefficients", StatementSource.WithoutFormula(),
                "For any Boolean function f on the entire binary word space, its coefficient at a is the integer sum over every x of sign(f(x)+dot(a,x)).", DescribeRole.Definition),
            Node("sign_add", "Signs multiply across binary addition", StatementSource.WithoutFormula(),
                "For binary exponents a and b, sign(a+b) equals sign(a) times sign(b) as an integer identity. The trace and Walsh expansions use this exact multiplicative character law.", DescribeRole.Lemma),
            Node("walsh_inversion", "Exact integer Walsh inversion", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.InversionFormula()),
                "For every positive length n, every Boolean f and every word y, summing walsh(f,a) sign(dot(a,y)) over all a gives the number of binary words times sign(f(y)). Character orthogonality is applied to an actual AddChar into the integers; this is an integer identity without a choice of normalization.", DescribeRole.Theorem),
            Node("walsh_support_nonempty", "The spectral support is nonempty", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.NonemptyFormula()),
                "At every positive length, every Boolean f has a nonzero integer Walsh coefficient. Otherwise inversion at the zero word would equate zero to the nonzero product of the number of words and an integer sign.", DescribeRole.Theorem),
            Node("inverseComponent", "An arbitrary component of the inverse", StatementSource.WithoutFormula(),
                "For arbitrary mask b at length 2m+1, the inverse component at y is dot(b,inverse(m,y)). The mask is unrestricted in this definition.", DescribeRole.Definition),
            Node("inverse_phase_sum", "The exact inverse-component orientation", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.PhaseFormula()),
                "For every m and all masks b,a, the sum over x of sign(dot(b,x)+dot(a,chi(x))) is the Walsh coefficient at a of the inverse component associated with b. Reindex by the proved bijection chi and use its left inverse identity. Zero and all-one masks are included.", DescribeRole.Theorem),
            Node("walsh_constant_derivative_iff", "Constant Boolean derivatives and Walsh support", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.WalshDerivativeFormula()),
                "For every positive length, a Boolean derivative in direction u is the constant c exactly when every nonzero Walsh coefficient is supported on the character level dot(a,u)=c. This is the exact two-way character statement; identifying the affine-span dimension still requires a separate argument.", DescribeRole.Theorem),
            Node("dotDual", "The dot-product dual map", StatementSource.WithoutFormula(),
                "Send a direction u to the linear functional a ↦ dot(a,u) on the binary word space.", DescribeRole.Definition),
            Node("dotDualEquiv", "Nondegenerate binary dot pairing", StatementSource.WithoutFormula(),
                "The dot-product map is a linear equivalence between the word space and its algebraic dual. Injectivity is checked on every coordinate vector and finite-dimensionality supplies surjectivity; this is the nondegenerate pairing used by the affine bridge.", DescribeRole.Definition),
            Node("walshSupportDirection", "Affine direction of Walsh support", StatementSource.WithoutFormula(),
                "Take the direction of the affine span over ZMod 2 of the nonzero Walsh support.", DescribeRole.Definition),
            Node("constantDerivativeSubmodule", "Constant-derivative submodule", StatementSource.WithoutFormula(),
                "Define the derivative directions as the comap of the dual annihilator of the Walsh-support affine direction along the dot-product dual map.", DescribeRole.Definition),
            Node("constantDerivative_affineSpan_duality", "Affine-span and dual-annihilator bridge", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.AffineDualityFormula()),
                "For every positive length and Boolean function, membership in the canonical constant-derivative submodule is equivalent to having a constant Boolean derivative. Its finrank plus the finrank of the Walsh-support affine direction equals the finrank of the full word space. The proof uses a nonzero Walsh coefficient as an affine base point, identifies the direction with the span of support differences, applies walsh_constant_derivative_iff, and transports the dual-annihilator finrank identity through the nondegenerate dot pairing. Length one is included by the same statement.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string name, string title, StatementSource statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cyclic-sign-trace-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(SourceNote),
            Blocks(Paragraph(Text(prose))), role);
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
