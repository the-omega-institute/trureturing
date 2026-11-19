using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class MeasurableRelativeDuhamelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original measurable nonautonomous Dyson–Phillips evolutions obey both ordered relative Duhamel identities, with actual vector Bochner integrability under separate vectorwise almost everywhere strong measurability and integrable scalar controls.",
        H("Relative Duhamel identities for measurable coefficients"), Blocks(
            Paragraph(Text("Let E be a complex Banach space in an arbitrary universe, including the zero space. Let S be the original NonautonomousDysonPhillips.Contraction E: a strongly continuous semigroup of bounded complex-linear contractions on nonnegative real times, with identity at zero. Write A(t)=S.action(t). Fix any real T>=0. For each real s, B(s) and H(s) are bounded complex-linear endomorphisms of E. For every fixed vector z separately, B(s)z and H(s)z are AE strongly measurable for real Lebesgue measure volume restricted to Icc(0,T). Let g and h be arbitrary nonnegative real functions integrable on this closed interval, with norm(B(s))<=g(s) and norm(H(s))<=h(s) at each point there.")),
            Paragraph(Text("For any coefficient Q write U_Q(t,r)=MeasurableNonautonomousDysonPhillips.measurableEvolution(S,Q,t,r). This is the same coefficient-indexed linear realization of the original NonautonomousDysonPhillips.sum, whose summands are the original ordered vector Bochner terms. The existential family in measurable_evolution is identified with this native family using its HasSum clause and measurableEvolution_apply. No new evolution is chosen.")),
            Describe.Lean(DescribeId.Create("both-relative-bochner-identities"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/MeasurableRelativeDuhamel.relative_duhamel"),
                H("Both ordered identities and both actual integrabilities"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real 0<=r<=t<=T and every vector x, both displayed vector integrands are IntervalIntegrable for volume from r to t. The difference U_(B+H)(t,r)x-U_B(t,r)x equals each actual interval integral. The order of all three factors is retained; B and H need not commute with each other, with the free semigroup, or at different times.")),
                    Paragraph(Text("First take any Bochner-integrable forcing f on Icc(r,T). Strong joint continuity of the native evolution on each fixed vector and its uniform exponential bound imply actual integrability of U_B(t,s)f(s) and continuity of its integral J(t) as the endpoint varies. To apply dominated parameter integration, extend the kernel by projecting both times into Icc(0,T) and replacing the upper time by the maximum of the two projected times. This bounded, strongly continuous extension agrees with the native evolution on every ordered integration interval. Extend f by zero only for that continuity argument.")),
                    Paragraph(Text("The forced mild identity is J(t)=integral from r to t of A(t-s)f(s), plus the integral from r to t of A(t-q)B(q)J(q). Insert the original homogeneous mild equation into U_B(t,s)f(s). On the square Icc(r,t) times Icc(r,t), the mixed vector integrand A(t-q)B(q)U_B(q,s)f(s), restricted to s<=q, is AE strongly measurable. Fixed-vector measurability and the existing measurable-evaluation theorem apply successively to the kernel and coefficient. Its norm is bounded by g(q) times exp(integral from 0 to T of g) times norm(f(s)); the product of the two scalar integrable functions is integrable for the product measure. Bochner Fubini therefore exchanges the two actual triangular integrals. Bounded complex-linear maps commute with the inner actual integral. No joint measurability premise is supplied externally.")),
                    Paragraph(Text("For the first order choose X(s)=U_(B+H)(s,r)x and f(s)=H(s)X(s). The native continuous vector path X and the scalar h control make this actual forcing integrable. Subtract the homogeneous B mild equation and the forced mild equation from the homogeneous B+H equation. The continuous residual X-U_B(.,r)x-J equals its own B causal integral. The existing continuous_residual_eq_zero theorem forces it to vanish: repeated causal integration gives the factorial estimate, whose bound tends to zero as the iteration index tends to infinity. This establishes the first exact reconstruction.")),
                    Paragraph(Text("Apply that same result with base B+H and increment -H, controlled respectively by g+h and h. Since (B+H)+(-H)=B, linearity and negation of the actual Bochner integral give the second order. This step changes the base; it never commutes factors.")),
                    Paragraph(Text("The hypotheses include trivial E, x=0, zero horizon, zero controls and all diagonal times r=t. The proof neither divides by a control mass nor requires norm(identity)=1. There is no finite-dimensionality or separability assumption, no operator-norm measurability, continuity or integrability, no common exceptional set over uncountably many vectors, no generator-domain condition and no regularity outside the horizon. These identities alone assert no first-response formula, exponential-tail estimate, quadratic remainder or uniform signed derivative.")),
                    Paragraph(Text("This is the classical variation-of-constants mechanism expressed for the original measurable Dyson–Phillips family. Mathlib supplies Bochner dominated parameter integration and Fubini for integrable product functions. The native terms, realization, exponential bounds, strong joint continuity, homogeneous mild equation and factorial residual uniqueness are reused from the existing nonautonomous development. No literature-priority assertion is made."))), DescribeRole.Theorem))));

    private static Formula R => Call("Real");
    private static Formula E => F.Id("E");
    private static Formula Z => new Formula.Number(0);
    private static Formula X(string n) => F.Id(n);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(X(n), Colon, d), Mapsto, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Clm => Call("ComplexCLM", E, E);
    private static Formula Coeff => Arrow(R, Clm);
    private static Formula J => Call("Icc", Z, X("T"));
    private static Formula Mu => Call("restrict", Call("volume"), J);
    private static Formula Meas(Formula q) => All("z", E, Call("AEStronglyMeasurable", Lam("s", R, At(At(q, X("s")), X("z"))), Mu));
    private static Formula Nonneg(Formula k) => All("s", R, Imp(Call("Mem", X("s"), J), Le(Z, At(k, X("s")))));
    private static Formula Bound(Formula q, Formula k) => All("s", R, Imp(Call("Mem", X("s"), J), Le(new Formula.Norm(At(q, X("s"))), At(k, X("s")))));
    private static Formula U(Formula q, Formula t, Formula r, Formula x) => Call("measurableEvolution", X("S"), q, t, r, x);
    private static Formula Integrand(bool second)
    {
        Formula b = X("B"), q = Add(b, X("H")), s = X("s");
        return Lam("s", R, U(second ? q : b, X("t"), s,
            At(At(X("H"), s), U(second ? b : q, s, X("r"), X("x")))));
    }
    private static Formula Statement()
    {
        Formula b = X("B"), h = X("H"), g = X("g"), k = X("h");
        Formula diff = Subtract(U(Add(b, h), X("t"), X("r"), X("x")), U(b, X("t"), X("r"), X("x")));
        Formula integral(bool second) => Call("intervalIntegral", Call("volume"), X("r"), X("t"), Integrand(second));
        Formula integrable(bool second) => Call("IntervalIntegrable", Integrand(second), Call("volume"), X("r"), X("t"));
        Formula result = And(integrable(false), And(integrable(true), And(Eq(diff, integral(false)), Eq(diff, integral(true)))));
        result = All("r", R, All("t", R, Imp(Le(Z, X("r")), Imp(Le(X("r"), X("t")), Imp(Le(X("t"), X("T")), All("x", E, result))))));
        Formula premises = Imp(Meas(b), Imp(Meas(h), All("g", Arrow(R, R), All("h", Arrow(R, R),
            Imp(Call("IntegrableOn", g, J, Call("volume")), Imp(Call("IntegrableOn", k, J, Call("volume")),
            Imp(Nonneg(g), Imp(Nonneg(k), Imp(Bound(b, g), Imp(Bound(h, k), result))))))))));
        return All("u", Call("Universe"), All("E", Call("Type", X("u")),
            Seq(OpenBracket, Call("NormedAddCommGroup", E), CloseBracket, Sp,
                OpenBracket, Call("NormedSpace", Call("Complex"), E), CloseBracket, Sp,
                OpenBracket, Call("CompleteSpace", E), CloseBracket, Sp,
                All("S", Call("Contraction", E), All("B", Coeff, All("H", Coeff,
                    All("T", R, Imp(Le(Z, X("T")), premises))))))));
    }
}
