using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean;

internal sealed class CyclicSignTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered integer sign-matrix trace equals its cyclic Boolean phase sum at every positive length. The cyclic Boolean map has an explicit inverse at every positive odd length, where integer Walsh inversion supplies nonempty trace support.",
        H("Odd cyclic Boolean inversion and the sign-matrix trace"),
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
                "For every natural m and every nonzero b of length 2m+1, the direction of the affine span over ZMod 2 of the trace support has dimension at least 2m. The parameter m runs from zero, so this is exactly all positive odd lengths, including length one. The inequality is a lower bound, not an equality. This definition states the question; the trace, inverse and Walsh results below do not prove its dimension bound.", DescribeRole.Definition),
            Node("alternatingPrefix", "Alternating products", StatementSource.WithoutFormula(),
                "The alternating prefix at i of length t is the product, for r from zero through t-1, of 1+y_(i+2r+1). The empty product is one.", DescribeRole.Definition),
            Node("inverse", "The inverse polynomial", StatementSource.WithoutFormula(),
                "At length 2m+1, the inverse coordinate at i is the sum, for r from zero through m, of y_(i+2r) times the alternating prefix at i of length r. Thus its first term is y_i.", DescribeRole.Definition),
            Node("inverse_spec", "Both inverse identities at every positive odd length", StatementSource.FromAuthor(InverseFormula()),
                "For every m, applying the inverse polynomial after chi gives the original word, and applying chi after the inverse polynomial does the same. The proof does not assume either identity or invertibility.", DescribeRole.Theorem),
            Paragraph(Text("Write y=chi(x). The local Boolean identity is x_i=y_i+(1+y_(i+1))x_(i+2). Iterating t times gives the first t terms of the inverse polynomial plus the alternating prefix of length t times x_(i+2t). For t=m+1 the latter x-coordinate is x_(i+1). If this tail were nonzero, x_(i+1) would be one and the m+1 alternating y-coordinates would all vanish. At each of these positions the recurrence forces the next intervening y-coordinate to vanish and the next x-coordinate in steps of two to be one. The even and odd representatives together cover the cycle, hence y=0.")),
            Paragraph(Text("When chi(x)=0 the recurrence makes x invariant under addition of two. Multiplication by m+1 is an inverse to multiplication by two modulo 2m+1, so every index is reached and x is constant. The image under chi of a constant binary word is that same constant word. Thus the zero fiber contains only the zero word, contradicting the tail's x-coordinate being one. This proves the left inverse identity. The finite domain and codomain have the same cardinality, so injectivity gives surjectivity and hence the right inverse identity.")),
            Node("dot", "Binary dot products", StatementSource.WithoutFormula(),
                "The dot product of a and x is the sum over all cyclic indices of a_i x_i in ZMod 2.", DescribeRole.Definition),
            Node("walsh", "Unnormalized integer Walsh coefficients", StatementSource.WithoutFormula(),
                "For any Boolean function f on the entire binary word space, its coefficient at a is the integer sum over every x of sign(f(x)+dot(a,x)).", DescribeRole.Definition),
            Node("walsh_inversion", "Exact integer Walsh inversion", StatementSource.FromAuthor(InversionFormula()),
                "For every positive length n, every Boolean f and every word y, summing walsh(f,a) sign(dot(a,y)) over all a gives the number of binary words times sign(f(y)). Character orthogonality is applied to an actual AddChar into the integers; this is an integer identity without a choice of normalization.", DescribeRole.Theorem),
            Node("walsh_support_nonempty", "The spectral support is nonempty", StatementSource.FromAuthor(NonemptyFormula()),
                "At every positive length, every Boolean f has a nonzero integer Walsh coefficient. Otherwise inversion at the zero word would equate zero to the nonzero product of the number of words and an integer sign.", DescribeRole.Theorem),
            Node("inverseComponent", "An arbitrary component of the inverse", StatementSource.WithoutFormula(),
                "For arbitrary mask b at length 2m+1, the inverse component at y is dot(b,inverse(m,y)). The mask is unrestricted in this definition.", DescribeRole.Definition),
            Node("inverse_phase_sum", "The exact inverse-component orientation", StatementSource.FromAuthor(PhaseFormula()),
                "For every m and all masks b,a, the sum over x of sign(dot(b,x)+dot(a,chi(x))) is the Walsh coefficient at a of the inverse component associated with b. Reindex by the proved bijection chi and use its left inverse identity. Zero and all-one masks are included.", DescribeRole.Theorem),
            Node("inverse_phase_support_nonempty", "The cyclic Boolean phase support is nonempty", StatementSource.FromAuthor(PhaseNonemptyFormula()),
                "For every natural m and every mask b, some a has a nonzero phase sum over x of sign(dot(b,x)+dot(a,chi(x))). This uses Walsh nonemptiness and the proved inverse reindexing. The trace identity below therefore also makes the literal source trace support nonempty, without any assumption on b.", DescribeRole.Theorem),
            Node("walsh_constant_derivative_iff", "Constant Boolean derivatives and Walsh support", StatementSource.FromAuthor(WalshDerivativeFormula()),
                "For every positive length, a Boolean derivative in direction u is the constant c exactly when every nonzero Walsh coefficient is supported on the character level dot(a,u)=c. This is the exact two-way character statement; identifying the affine-span dimension still requires a separate argument.", DescribeRole.Theorem),
            Node("dotDual", "The dot-product dual map", StatementSource.WithoutFormula(),
                "Send a direction u to the linear functional a ↦ dot(a,u) on the binary word space.", DescribeRole.Definition),
            Node("dotDualEquiv", "Nondegenerate binary dot pairing", StatementSource.WithoutFormula(),
                "The dot-product map is a linear equivalence between the word space and its algebraic dual. Injectivity is checked on every coordinate vector and finite-dimensionality supplies surjectivity; this is the nondegenerate pairing used by the affine bridge.", DescribeRole.Definition),
            Node("walshSupportDirection", "Affine direction of Walsh support", StatementSource.WithoutFormula(),
                "Take the direction of the affine span over ZMod 2 of the nonzero Walsh support.", DescribeRole.Definition),
            Node("constantDerivativeSubmodule", "Constant-derivative submodule", StatementSource.WithoutFormula(),
                "Define the derivative directions as the comap of the dual annihilator of the Walsh-support affine direction along the dot-product dual map.", DescribeRole.Definition),
            Node("constantDerivative_affineSpan_duality", "Affine-span and dual-annihilator bridge", StatementSource.FromAuthor(AffineDualityFormula()),
                "For every positive length and Boolean function, membership in the canonical constant-derivative submodule is equivalent to having a constant Boolean derivative. Its finrank plus the finrank of the Walsh-support affine direction equals the finrank of the full word space. The proof uses a nonzero Walsh coefficient as an affine base point, identifies the direction with the span of support differences, applies walsh_constant_derivative_iff, and transports the dual-annihilator finrank identity through the nondegenerate dot pairing. Length one is included by the same statement.", DescribeRole.Theorem),
            Node("sourceTrace_eq_phase_sum", "The ordered trace is the exact Boolean phase sum", StatementSource.FromAuthor(TracePhaseFormula()),
                "At every positive length n and for all words b,a, the literal ordered matrix trace is the sum over every x of sign(dot(b,x)+dot(a,chi(x))). Length one and all coincident cyclic indices are included. This identity also applies to even lengths; oddness is needed only for the inverse construction.", DescribeRole.Theorem),
            Paragraph(Text("For a list of r+1 matrices, expand its (i,j) entry over all r intermediate states. The row tuple is i followed by the intermediate states; the column tuple is those states followed by j. Induction uses the first matrix factor and the ordinary Matrix.mul entry formula, preserving the complete list order. Taking the trace identifies j with i. Joining the initial state to the intermediate tuple gives every cyclic path exactly once; the final column is the initial state, including for a one-factor product.")),
            Paragraph(Text("The path product is the sign of the sum of its entry exponents. Reindex the a_(k-2)x_k term by k=i+2 and the a_(k-1)x_k x_(k+1) term by k=i+1. The coefficient of a_i becomes x_i+x_(i+2)+x_(i+1)x_(i+2), exactly chi(x)_i. These are bijections of the actual cyclic index set, so repeated indices need no separate independence assumption. Combining this identity with the inverse phase formula identifies traceSupport(b) with the nonzero Walsh support of inverseComponent(m,b) at every odd length. The established phase nonemptiness thus supplies trace nonemptiness.")),
            Node("booleanMonomial", "Squarefree Boolean monomials", StatementSource.WithoutFormula(),
                "For a finite set s of actual cyclic coordinates, booleanMonomial(s,z) is the product of z_i over i in s. Repeated cyclic coordinates are represented only once; the empty monomial is one.", DescribeRole.Definition),
            Node("indicatorWord", "Indicator words", StatementSource.WithoutFormula(),
                "The word indicatorWord(s) is one at coordinates in s and zero elsewhere.", DescribeRole.Definition),
            Node("booleanCoeff", "Coefficients from actual function values", StatementSource.WithoutFormula(),
                "The coefficient of a Boolean function f at s is the sum in ZMod 2 of f(indicatorWord(t)) over every subset t of s. Thus equal actual functions have equal coefficients. Subset cancellation proves that extraction applied to the monomial at t is one exactly when s=t and zero otherwise; this establishes uniqueness for finite sums of squarefree monomials without assuming injectivity of polynomial evaluation.", DescribeRole.Definition),
            Node("prefixVariables", "Cyclic prefix variable sets", StatementSource.WithoutFormula(),
                "The finite set prefixVariables(i,r) is the image of t=0,...,r-1 under t ↦ i+2t+1 in the actual cyclic index type.", DescribeRole.Definition),
            Node("inverse_component_boolean_coefficient", "Exact coefficients of the shifted inverse component", StatementSource.FromAuthor(BooleanCoefficientFormula()),
                "For every m, mask b and finite cyclic-coordinate set s, extract the coefficient of z ↦ inverseComponent(m,b)(1+z). Each inverse term contributes the prefix monomial and the prefix with its endpoint i+2r inserted, weighted by b_i. Equality of finite sets decides whether each contributes at s. This statement includes all masks and length one, with no distinct-index premise.", DescribeRole.Theorem),
            Paragraph(Text("Binary idempotence identifies a product over repeated coordinates with its squarefree monomial. After y=1+z the alternating prefix becomes the monomial on prefixVariables(i,r), and its endpoint factor is 1+z_(i+2r). The coefficient formula follows by linearity of extraction and the subset-cancellation identity. No Boolean normal-form uniqueness or coefficient vanishing is assumed.")),
            Node("monomialDerivativeCoeff", "Exact monomial derivative coefficients", StatementSource.WithoutFormula(),
                "At variable sets t,s and direction u, this is the product of u on t minus s when s is a subset of t, plus one when s=t; absent contributions are zero. Product expansion and coefficient extraction prove that this is the coefficient at s of z ↦ booleanMonomial(t,z+u)+booleanMonomial(t,z).", DescribeRole.Definition),
            Node("inverse_component_derivative_coefficients", "Necessary coefficient equations for a constant inverse derivative", StatementSource.FromAuthor(DerivativeCoefficientFormula()),
                "For every m, b,u and nonempty finite set s, if the derivative of the actual inverse component in direction u is constant on all words, the displayed sum of its monomial derivative coefficients is zero. The proof translates by the all-one word and extracts the coefficient from actual functions. It assumes neither a degree argument nor the intended mask classification.", DescribeRole.Theorem),
            Node("topVariables", "Highest-degree cyclic variable sets", StatementSource.WithoutFormula(),
                "The set topVariables(m,i) is prefixVariables(i,m) with coordinate i+2m inserted. It has m+1 elements. Its coordinate sum has slope m+1 as a function of i; multiplication by two in the odd cycle inverts that slope, so the sets for distinct i are distinct.", DescribeRole.Definition),
            Node("inverse_component_top_coefficient", "Highest-degree coefficients recover every mask bit", StatementSource.FromAuthor(TopCoefficientFormula()),
                "For every m, b and cyclic coordinate i, the coefficient of the shifted inverse component at topVariables(m,i) is exactly b_i. Cardinality excludes every shorter prefix and endpoint term; injectivity of the highest-degree variable sets leaves exactly the term indexed by i. Length one and zero masks are included.", DescribeRole.Theorem),
            Node("inverse_component_top_derivative", "The degree-m derivative equation", StatementSource.FromAuthor(TopDerivativeFormula()),
                "For every positive m and constant derivative direction u of the inverse component, and every finite coordinate set s of cardinality m, the sum over i of b_i times the product of u on topVariables(m,i) minus s, with zero contribution unless s is a subset, vanishes. A derivative of a monomial of degree at most m has zero degree-m coefficient; hence only the degree-(m+1) endpoint terms survive. The statement includes m=1 but does not claim the subsequent overlap classification.", DescribeRole.Theorem),
            Paragraph(Text("The literal trace model follows ricardorr, MathOverflow question 512655, original revision E06A6743-2C15-41CD-9390-04D1862ABA02, https://mathoverflow.net/questions/512655, attributed under CC-BY-SA 4.0. The inverse argument above is a direct derivation for this cyclic map.")),
            Paragraph(Text("The affine-span duality is proved above. The affine-support assertion still requires the complete classification of constant derivative directions for every nonzero inverse-component mask, including the cyclic top-overlap and lower-coefficient arguments for lengths at least five, the length-three polar case and assembly with length one. The coefficient formula alone does not establish that classification or settle the dimension bound."))
        ), []));

    private static DocumentBlock Node(string name, string title, StatementSource statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cyclic-sign-trace-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
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

    private static Formula InverseFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"),
            And(All("x", w, Eq(Call("inverse", m, Call("chi", x)), x)),
                All("y", w, Eq(Call("chi", Call("inverse", m, y)), y)))));
    }
    private static Formula InversionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), y = F.Id("y"), a = F.Id("a"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), All("y", w,
                Eq(Sum("a", w, Times(Call("walsh", f, a), Call("sign", Call("dot", a, y)))),
                    Times(Call("card", w), Call("sign", Call("f", y)))))))));
    }
    private static Formula NonemptyFormula()
    {
        Formula n = F.Id("n"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), Some("a", w,
                Rel(Call("walsh", F.Id("f"), F.Id("a")), FormulaRelationOperator.NotEqual, D(0)))))));
    }
    private static Formula PhaseNonemptyFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, Some("a", w,
            Rel(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                FormulaRelationOperator.NotEqual, D(0))))));
    }
    private static Formula PhaseFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, All("a", w,
            Eq(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                Call("walsh", Call("inverseComponent", m, b), a))))));
    }
    private static Formula TracePhaseFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("b", w, All("a", w,
                Eq(Call("sourceTrace", b, a),
                    Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x)))))))))));
    }
    private static Formula WalshDerivativeFormula()
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
    private static Formula AffineDualityFormula()
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
    private static Formula BooleanCoefficientFormula()
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
    private static Formula DerivativeCoefficientFormula()
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
    private static Formula TopCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), i = F.Id("i"), n = OddLength(m);
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("i", Call("ZMod", n),
            Eq(Call("booleanCoeff", shifted, Call("topVariables", m, i)), Call("b", i))))));
    }
    private static Formula TopDerivativeFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), y = F.Id("y"), n = OddLength(m), t = Call("topVariables", m, i);
        Formula constant = Some("c", Call("ZMod", D(2)), All("y", Word(n),
            Eq(Plus(Call("inverseComponent", m, b, Plus(y, u)), Call("inverseComponent", m, b, y)), F.Id("c"))));
        Formula summand = Times(Call("b", i), Call("ite", Call("subset", s, t),
            Call("booleanMonomial", Call("sdiff", t, s), u), D(0)));
        return Disp(All("m", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, m),
            All("b", Word(n), All("u", Word(n), Imp(constant,
                All("s", Call("Finset", Call("ZMod", n)), Imp(Eq(Call("card", s), m),
                    Eq(Sum("i", Call("ZMod", n), summand), D(0)))))))));
    }
}
