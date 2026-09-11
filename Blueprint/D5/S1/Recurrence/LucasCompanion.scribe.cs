using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LucasCompanionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LucasCompanion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/fiebigmbirikaspilker2025lucas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Companion traces, equality of periods when two is a unit, and the dyadic positive-zero criterion; "
            + "Questions 5.3 and 5.4 remain outside this module's scope.",
        H("Lucas Companion Traces and Dyadic Zeros"),
        Blocks(
            Paragraph(Text(
                "The companion sequence V is realized as trace(M^n), where M is the "
                    + "invertible companion matrix underlying U. Integer indices come "
                    + "from zpow. This module proves that the least period of V equals "
                    + "the matrix order when 2 is invertible and V has a zero. For even "
                    + "integer p and odd integer q it also proves the exact valuations "
                    + "v₂(V(2j)) = 1 and v₂(V(2j+1)) = v₂(p), and, for v ≥ 2, the "
                    + "existence of a positive zero modulo 2^v exactly when 2^v divides p, "
                    + "with index 1 as witness. These arithmetic assertions concern "
                    + "natural indices and include p = 0, with mathlib's v₂(0) = 0 convention.")),
            Paragraph(Text(
                "This does not settle Questions 5.3 or 5.4 of Fiebig, Mbirika and "
                    + "Spilker. They ask whether the periods of U and V agree when "
                    + "p and the modulus are both even. The module supplies the base "
                    + "layer and one of the two ingredients; multiplicativity of the "
                    + "period over a coprime factorization and the assembly are not here. "
                    + "The paper's exceptional case is q = 1, modulus 4, and 4 dividing p. "
                    + "The zero criterion explains where that condition comes from, "
                    + "but the exception itself is a statement about periods and is "
                    + "out of scope for this module.")),
            Paragraph(Text(
                "Every theorem below is proved in the repository. The paper supplies "
                    + "the vocabulary of the companion recurrence and entry point: "
                    + "the entry point is the least positive zero index, if one exists. "
                    + "The two recurrence nodes cite that vocabulary and those initial "
                    + "values and recurrence equations. Their extensions to the full "
                    + "displayed parameter domains are proved here. The trace definitions, "
                    + "period constructions, and remaining results are repository work; "
                    + "literature attribution does not pass along their dependencies.")),
            Paragraph(Text(
                "In the displays U(p,q,n) is LucasEvenDescent.lucasU, V(p,q,n) is "
                    + "lucasV, and W(p,q,n) is lucasVInt. M(p,q) is "
                    + "LucasEvenDescent.companion, while A(p,q,n) abbreviates "
                    + "val(M(p,q)^n), the private powerMatrix definition unfolded. "
                    + "Mat2(R) means Matrix (Fin 2) (Fin 2) R, with labels 0 and 1; "
                    + "Units(R) means Rˣ and val is its coercion. Cast denotes the "
                    + "canonical cast. piM and piV denote matrixPeriod and companionPeriod. "
                    + "Per(p,q,k) means that V(p,q,n+k) = V(p,q,n) for every integer n. "
                    + "S_R is the shift on functions from the integers to R, defined by "
                    + "S_R(f)(n) = f(n+1). Its minimalPeriod at a function is zero if "
                    + "there is no positive return time; orderOf uses the analogous "
                    + "zero convention for infinite order. v₂(x) abbreviates "
                    + "padicValInt 2 x. Type* allows any universe, and bracketed binders "
                    + "retain the Lean typeclass hypotheses.")),
            Node("lucasV", "The bilateral companion trace", LucasVFormula(),
                "Taking the trace of a power of the companion unit defines the "
                    + "sequence at every integer index over any commutative ring.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("companion_power_shape", "The shape of every integer companion power",
                PowerShapeFormula(),
                "Commutation with M determines the off-diagonal and lower-right "
                    + "entries. Multiplication by M identifies the upper-left entry "
                    + "with U(n+1). The displayed A is the unfolded private definition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companion_power_det", "The determinant at integer powers",
                RingAt("n", Equal(Call("det", A(N())), Val(Power(Q(), N())))),
                "The determinant homomorphism sends M to q and respects integer "
                    + "powers of units, including negative powers.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasV_eq_lucasU", "The trace expressed through U",
                RingAt("n", Equal(V(N()), Sub(Mul(D(2), U(Add(N(), D(1)))), Mul(P(), U(N()))))),
                "Add the diagonal entries in the power-shape identity. This is "
                    + "the bridge used to transfer the frozen recurrence to the trace.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasV_recurrence", "The companion initial values and bilateral recurrence",
                RecurrenceFormula(false),
                "The cited paper defines the companion sequence by V(0)=2, V(1)=p "
                    + "and this recurrence. Here its trace realization is proved to "
                    + "satisfy those equations over every commutative ring with unit q, "
                    + "at all integer indices. That general algebraic extension is "
                    + "established here, without the paper's standing parameter restrictions. "
                    + "The paper's entry point, when it exists, is its least positive zero index.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("lucasV_determinant_identity", "The companion quadratic determinant identity",
                DeterminantFormula(),
                "Substitute the bridge to U into the companion-power determinant "
                    + "identity and use the recurrence. The right side retains the "
                    + "unit power q^n and the discriminant p^2-4q.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companion_double_of_lucasV_zero", "A zero trace gives a scalar double power",
                DoubleZeroFormula(),
                "Apply the two-by-two Cayley--Hamilton identity to A(r). The zero "
                    + "trace removes its linear term, leaving the negative determinant "
                    + "times the identity matrix. smul denotes scalar multiplication.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("matrixPeriod", "The order of the companion unit",
                RingDisplay(Seq(Equal(PiM(), Call("orderOf", M())), Sp, InMacro, Sp, Naturals())),
                "This noncomputable repository definition is the order of M in "
                    + "the matrix unit group. It may be zero without finiteness.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("companion_zpow_eq_one_iff", "Identity powers are period multiples",
                RingAt("k", Seq(Equal(Power(M(), K()), D(1)), Sp, Iff, Sp,
                    Divides(Cast(PiM(), Integers()), K()))),
                "The integer-power order theorem characterizes every identity "
                    + "power, with no finite-ring assumption.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("matrixPeriod_pos", "Positive matrix period over a finite ring",
                FiniteRingDisplay(Positive(PiM())),
                "Finiteness makes the companion unit have positive order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("matrixPeriod_zmod_pos", "Positive matrix period modulo a positive modulus",
                ZModPeriodFormula(),
                "The positive-modulus hypothesis supplies NeZero m and hence "
                    + "the finite-ring instance for ZMod m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasV_periodic", "Matrix periodicity passes to the trace",
                RingDisplay(Per(Cast(PiM(), Integers()))),
                "The companion power at its order is the identity, so translating "
                    + "any integer index by that order leaves the trace unchanged.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companionPeriod", "The minimal return time under the shift",
                CompanionPeriodFormula(),
                "Apply Function.minimalPeriod to the shift on the entire bilateral "
                    + "sequence. This is a repository construction; a zero value "
                    + "is allowed when the sequence has no positive period.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("companionPeriod_dvd_iff", "Natural periods are minimal-period multiples",
                RingDisplay(Seq(Bind("k", Naturals()), Sp,
                    Divides(PiV(), K()), Sp, Iff, Sp, Per(Cast(K(), Integers())))),
                "Iterating the shift k times translates by k. The minimal-period "
                    + "divisibility theorem therefore applies to all natural "
                    + "translation periods, including zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companionPeriod_dvd_matrixPeriod", "The companion period divides the matrix period",
                RingDisplay(Divides(PiV(), PiM())),
                "Combine trace periodicity with the divisibility characterization.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companionPeriod_spec", "The least positive companion period over a finite ring",
                PeriodSpecFormula(),
                "A divisor of the positive matrix period is positive. The same "
                    + "characterization proves periodicity at piV and its minimality "
                    + "among positive natural periods; all three conclusions are retained.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("companionPeriod_eq_matrixPeriod_of_lucasV_zero", "Equality of periods from a zero and invertible two",
                PeriodEqualityFormula(),
                "This generalizes the odd-modulus branch of the published Corollary 3.13 "
                    + "to any commutative ring in which two is invertible, and proves it "
                    + "directly. It does not cover the branch in which the parameter is "
                    + "odd and the modulus is even, where two is not invertible. The "
                    + "hypotheses are that 2 is a unit and V has an integer zero, with "
                    + "no restriction on q beyond its unit type and no finiteness "
                    + "assumption. Commutation "
                    + "and translation at the zero give a two-by-two linear system; "
                    + "its determinant is the unit -q^r. Cancellation forces the "
                    + "companion power at piV to be the identity. This direct proof "
                    + "removes both external dependencies of the published argument: "
                    + "Ballot's theorem and McDaniel's 1991 gcd theorem.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt", "Natural traces for arbitrary integer parameters",
                LucasVIntFormula(),
                "Natural matrix powers require no inverse. W therefore allows "
                    + "every integer q, including nonunits, while retaining integral values.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lucasVInt_eq_lucasV", "Agreement at natural indices for unit q",
                IntegerBridgeFormula(),
                "A unit's natural power agrees with its integer power at the "
                    + "cast index. Unfold both traces and the companion definition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt_recurrence", "The integral companion recurrence without a unit restriction",
                RecurrenceFormula(true),
                "The paper's companion sequence has these initial values and "
                    + "recurrence. The repository proves them for every integer p "
                    + "and q by multiplying the matrix identity M^2=pM-qI by M^n "
                    + "and taking traces. The unrestricted parameter extension and "
                    + "its proof are repository work.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("lucasVInt_two_adic_congruences", "Simultaneous dyadic congruences for W",
                CongruencesFormula(false),
                "A paired recurrence induction works whenever the modulus divides "
                    + "p^2. Evenness of p supplies that divisibility for 2^(v₂(p)+1). "
                    + "No oddness or unit assumption on q is required for these congruences.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt_even_two_adic_valuation", "Even terms of W have valuation one",
                ValuationFormula(false, false),
                "For even p and odd q the paired factorization writes W(2j) as "
                    + "2 times an odd integer. Its valuation is exactly one, "
                    + "including at j=0 and p=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt_odd_two_adic_valuation", "Odd terms of W have the valuation of p",
                ValuationFormula(false, true),
                "The paired factorization writes W(2j+1) as p times an odd "
                    + "integer. The proof handles p=0 separately, retaining "
                    + "mathlib's zero convention for padicValInt.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt_exists_positive_zero_iff", "The exact dyadic positive-zero criterion",
                PositiveZeroFormula(false, false),
                "This repository result is sharper than the paper's remark that "
                    + "the exceptional case needs 4 dividing p. For every v at least "
                    + "2, even-index terms cannot vanish modulo 2^v because their "
                    + "valuation is one; an odd-index zero forces 2^v to divide p, "
                    + "including the separate p=0 case. Conversely W(1)=p is a "
                    + "positive-index witness. This characterizes zeros, not the "
                    + "period exception or the unresolved period assembly.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasVInt_positive_zero_iff_index_one", "Index one witnesses every positive zero for W",
                PositiveZeroFormula(false, true),
                "Rewrite the divisibility criterion using W(1)=p. The result "
                    + "retains even p, odd q, and v at least 2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasV_exists_positive_zero_iff", "The dyadic positive-zero criterion for V",
                PositiveZeroFormula(true, false),
                "Specialize the integral criterion to unit q and cast each "
                    + "natural zero index into the bilateral index type.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucasV_positive_zero_iff_index_one", "Index one witnesses every positive zero for V",
                PositiveZeroFormula(true, true),
                "The criterion and V(1)=p identify existence of a positive "
                    + "natural zero with vanishing at index one, for v at least 2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("lucas-companion-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(string name, Formula type) => Seq(F.Id(name), Colon, Sp, type);
    private static Formula Bind(string name, Formula type) =>
        Seq(Forall, Sp, Typed(name, type), Comma);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula R() => F.Id("R");
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula Units(Formula ring) => Call("Units", ring);
    private static Formula Val(Formula unit) => Call("val", unit);
    private static Formula Cast(Formula value, Formula type) => Call("Cast", value, type);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Neg(Formula value) => new Formula.Negate(value);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Divides(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula Positive(Formula x) => Seq(D(0), Sp, Lt, Sp, x);
    private static Formula Even(Formula x) => Call("Even", x);
    private static Formula Odd(Formula x) => Call("Odd", x);
    private static Formula M() => Call("M", P(), Q());
    private static Formula A(Formula index) => Call("A", P(), Q(), index);
    private static Formula U(Formula index) => Call("U", P(), Q(), index);
    private static Formula V(Formula index) => Call("V", P(), Q(), index);
    private static Formula W(Formula index) => Call("W", P(), Q(), index);
    private static Formula PiM() => Call("piM", P(), Q());
    private static Formula PiV() => Call("piV", P(), Q());
    private static Formula Per(Formula period) => Call("Per", P(), Q(), period);
    private static Formula V2(Formula value) => Call("padicValInt", D(2), value);
    private static Formula RingContext() => Seq(
        Bind("R", Seq(F.Id("Type"), Star)), Sp,
        OpenBracket, Call("CommRing", R()), CloseBracket, Comma);
    private static Formula Parameters(Formula ring) => Seq(
        Bind("p", ring), Sp, Bind("q", Units(ring)));
    private static Formula FiniteContext() => Seq(
        Grp(), OpenBracket, Call("Finite", R()), CloseBracket, Comma);
    private static Formula RingDisplay(Formula body) => Disp(new Formula.Aligned([
        RingContext(), Parameters(R()), body,
    ]));
    private static Formula RingAt(string name, Formula body) => Disp(new Formula.Aligned([
        RingContext(), Parameters(R()), Bind(name, Integers()), body,
    ]));
    private static Formula FiniteRingDisplay(Formula body) => Disp(new Formula.Aligned([
        RingContext(), FiniteContext(), Parameters(R()), body,
    ]));
    private static Formula Matrix(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("bmatrix")), a, Amp, b, RowBreak, c, Amp, d,
        End, Grp(F.Id("bmatrix")));

    private static Formula LucasVFormula() => RingAt("n",
        Equal(V(N()), Call("trace", Val(Power(M(), N())))));

    private static Formula PowerShapeFormula() => RingAt("n", Equal(A(N()), Matrix(
        U(Add(N(), D(1))), Mul(Neg(Val(Q())), U(N())), U(N()),
        Sub(U(Add(N(), D(1))), Mul(P(), U(N()))))));

    private static Formula RecurrenceFormula(bool integral)
    {
        Formula Term(Formula index) => integral ? W(index) : V(index);
        Formula context = integral ? IntegerParameters(false) : RingContext();
        Formula parameters = integral ? Grp() : Parameters(R());
        Formula q = integral ? Q() : Val(Q());
        return Disp(new Formula.Aligned([
            context, parameters,
            Seq(Equal(Term(D(0)), D(2)), Sp, Land, Sp,
                Equal(Term(D(1)), P()), Sp, Land),
            Seq(Bind("n", integral ? Naturals() : Integers()), Sp,
                Equal(Term(Add(N(), D(2))),
                    Sub(Mul(P(), Term(Add(N(), D(1)))), Mul(q, Term(N()))))),
        ]));
    }

    private static Formula DeterminantFormula()
    {
        Formula next = V(Add(N(), D(1)));
        Formula left = Add(Sub(Power(next, D(2)), Mul(Mul(P(), V(N())), next)),
            Mul(Val(Q()), Power(V(N()), D(2))));
        Formula right = Mul(Neg(Val(Power(Q(), N()))),
            Paren(Sub(Power(P(), D(2)), Mul(D(4), Val(Q())))));
        return RingAt("n", Equal(left, right));
    }

    private static Formula DoubleZeroFormula()
    {
        Formula r = F.Id("r");
        return RingAt("r", Seq(Equal(V(r), D(0)), Sp, Rightarrow, Sp,
            Equal(A(Mul(D(2), r)), Call("smul", Neg(Val(Power(Q(), r))),
                Seq(D(1), Colon, Sp, Call("Mat2", R()))))));
    }

    private static Formula ZModPeriodFormula()
    {
        Formula m = F.Id("m");
        Formula ring = Call("ZMod", m);
        return Disp(new Formula.Aligned([
            Bind("m", Naturals()), Seq(Positive(m), Sp, Rightarrow),
            Parameters(ring), Positive(PiM()),
        ]));
    }

    private static Formula CompanionPeriodFormula() => RingDisplay(Seq(Equal(
        PiV(),
        Call("minimalPeriod", new Formula.Subscript(F.Id("S"), R()),
            Seq(Named("V"), Open, P(), Comma, Q(), Comma, Cdot, Close))),
        Sp, InMacro, Sp, Naturals()));

    private static Formula PeriodSpecFormula() => FiniteRingDisplay(Seq(
        Positive(PiV()), Sp, Land, Sp, Per(Cast(PiV(), Integers())), Sp, Land, Sp,
        Paren(Seq(Bind("k", Naturals()), Sp, Positive(K()), Sp, Rightarrow, Sp,
            Per(Cast(K(), Integers())), Sp, Rightarrow, Sp, PiV(), Sp, Leq, Sp, K()))));

    private static Formula PeriodEqualityFormula() => RingDisplay(Seq(
        Call("IsUnit", Seq(D(2), Colon, Sp, R())), Sp, Rightarrow, Sp,
        Paren(Seq(Exists, Sp, Typed("r", Integers()), Comma, Sp,
            Equal(V(F.Id("r")), D(0)))), Sp, Rightarrow, Sp, Equal(PiV(), PiM())));

    private static Formula IntegerParameters(bool unitQ) => Seq(
        Bind("p", Integers()), Sp, Bind("q", unitQ ? Units(Integers()) : Integers()));

    private static Formula LucasVIntFormula() => Disp(new Formula.Aligned([
        IntegerParameters(false), Bind("n", Naturals()),
        Equal(W(N()), Call("trace", Power(
            Paren(Seq(Matrix(P(), Neg(Q()), D(1), D(0)), Colon, Sp, Call("Mat2", Integers()))), N()))),
    ]));

    private static Formula IntegerBridgeFormula() => Disp(new Formula.Aligned([
        IntegerParameters(true), Bind("n", Naturals()),
        Equal(Call("W", P(), Val(Q()), N()), V(Cast(N(), Integers()))),
    ]));

    private static Formula ArithmeticHypotheses(bool unitQ, bool oddQ) => unitQ || !oddQ
        ? Seq(Even(P()), Sp, Rightarrow)
        : Seq(Even(P()), Sp, Rightarrow, Sp, Odd(Q()), Sp, Rightarrow);

    private static Formula ArithmeticTerm(bool unitQ, Formula naturalIndex) =>
        unitQ ? V(Cast(naturalIndex, Integers())) : W(naturalIndex);

    private static Formula Congruent(Formula x, Formula y, Formula modulus) => Seq(
        x, Sp, Equiv, Sp, y, Sp, Open, Named("mod"), Sp, modulus, Close);

    private static Formula CongruencesFormula(bool unitQ)
    {
        Formula q = unitQ ? Val(Q()) : Q();
        Formula t = F.Id("t");
        Formula modulus = Power(Paren(Seq(D(2), Colon, Sp, Integers())), Add(t, D(1)));
        Formula qPower = Power(Paren(Neg(q)), J());
        return Disp(new Formula.Aligned([
            IntegerParameters(unitQ), ArithmeticHypotheses(unitQ, false), Bind("j", Naturals()),
            Seq(Named("let"), Sp, Equal(t, V2(P())), Sp, Named("in")),
            Seq(Congruent(ArithmeticTerm(unitQ, Mul(D(2), J())), Mul(D(2), qPower), modulus),
                Sp, Land),
            Congruent(ArithmeticTerm(unitQ, Add(Mul(D(2), J()), D(1))),
                Mul(Mul(Paren(Add(Mul(D(2), Cast(J(), Integers())), D(1))), P()), qPower), modulus),
        ]));
    }

    private static Formula ValuationFormula(bool unitQ, bool oddIndex)
    {
        Formula index = oddIndex ? Add(Mul(D(2), J()), D(1)) : Mul(D(2), J());
        return Disp(new Formula.Aligned([
            IntegerParameters(unitQ), ArithmeticHypotheses(unitQ, true), Bind("j", Naturals()),
            Equal(V2(ArithmeticTerm(unitQ, index)), oddIndex ? V2(P()) : D(1)),
        ]));
    }

    private static Formula PositiveZeroFormula(bool unitQ, bool indexOne)
    {
        Formula v = F.Id("v");
        Formula r = F.Id("r");
        Formula modulus = Power(Paren(Seq(D(2), Colon, Sp, Integers())), v);
        return Disp(new Formula.Aligned([
            IntegerParameters(unitQ), ArithmeticHypotheses(unitQ, true),
            Seq(Bind("v", Naturals()), Sp, D(2), Sp, Leq, Sp, v, Sp, Rightarrow),
            Seq(Paren(Seq(Exists, Sp, Typed("r", Naturals()), Comma, Sp,
                Positive(r), Sp, Land, Sp, Divides(modulus, ArithmeticTerm(unitQ, r)))),
                Sp, Iff, Sp, Divides(modulus, indexOne ? ArithmeticTerm(unitQ, D(1)) : P())),
        ]));
    }
}
