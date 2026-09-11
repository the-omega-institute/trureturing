using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LucasEvenDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LucasEvenDescent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Periods/fiebigmbirikaspilker2025lucas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A machine-checked proof of Conjecture 5.2 on Lucas descent at all integer indices.",
        H("Lucas Descent for Even Moduli"),
        Blocks(
            Paragraph(Text(
                "Fiebig, Mbirika and Spilker state Conjecture 5.2 as open in Section 5 "
                    + "of their paper and attribute it there to Diego Garcia-Fernandezsesma, "
                    + "Oliver Lippard and aBa Mbirika. For even p and even positive m "
                    + "with gcd(q,m) = 1, "
                    + "the congruences U(2n) = 0 and U(2n+1) = q^n modulo m force exactly "
                    + "one of two alternatives: U(n) = 0, or U(n) = m/2 with n an odd "
                    + "integer multiple of half the entry point. This module proves the "
                    + "stronger implication at all integer indices: besides the two "
                    + "doubling hypotheses, it needs only a positive even modulus and "
                    + "a unit q. It needs none of the paper's standing restrictions on "
                    + "the parameters: nonzero parameters, coprimality of p and q, "
                    + "nondegeneracy, or parity of p.")),
            Paragraph(Text(
                "The sequence, the entry-point notion and the conjecture come from the "
                    + "literature. The repository realizes the recurrence by powers of an "
                    + "invertible companion matrix and defines the entry point from the "
                    + "subgroup of integer zero indices. The general ring identities and "
                    + "the subgroup formulation below are repository formulations; the "
                    + "two final statements carry the paper's attribution.")),
            Paragraph(Text(
                "In the displays, U(p,q,n) denotes lucasU p q n and e(p,q) denotes "
                    + "entryPoint p q. Mat2(R) means Matrix (Fin 2) (Fin 2) R, with row "
                    + "and column labels 0 and 1. Units(R) is the group Rˣ; val denotes "
                    + "its coercion to R (or to the matrix ring). Powers of units use "
                    + "integer exponents. Type* permits any universe, and bracketed "
                    + "binders retain the indicated Lean typeclass hypotheses. Cast(x,T) "
                    + "denotes the canonical cast to T. Div(x,2) denotes Lean's integer "
                    + "or natural division, as determined by the type of x; the evenness "
                    + "hypotheses make the halves in the conclusion exact.")),
            Node("companion", "The invertible companion matrix", CompanionFormula(),
                "The matrix has determinant q. Its displayed inverse uses the inverse "
                    + "of the unit q, so the construction needs only a commutative ring "
                    + "and supports negative powers as well as nonnegative powers.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lucasU", "The Lucas sequence from integer matrix powers", LucasFormula(),
                "Take the entry in row 1, column 0 of the n-th power of the companion "
                    + "unit. This is a repository realization of the paper's recurrence. "
                    + "Invertibility makes it meaningful for every integer n.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lucas_recurrence", "Initial values and recurrence at every integer index",
                RecurrenceFormula(),
                "Commuting a matrix power with the companion matrix determines all "
                    + "four entries in terms of U(n) and U(n+1). Multiplication by one "
                    + "more companion matrix gives the recurrence; the zeroth and first "
                    + "powers give U(0)=0 and U(1)=1. No sign restriction on n is used.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("two_mul_lucas_eq_zero", "The doubling hypotheses force two-torsion",
                TwoTorsionFormula(),
                "For arbitrary p, matrix multiplication gives both doubling identities, and the "
                    + "determinant gives the quadratic identity with right side q^n. "
                    + "Combining them under both displayed hypotheses yields "
                    + "(2U(n))q^n=0. Cancel the unit q^n. This step holds over any "
                    + "commutative ring, without a finiteness or modulus hypothesis.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("entryPoint", "The nonnegative generator of the zero indices",
                EntryPointFormula(),
                "The addition identity closes the zero indices under addition. At a "
                    + "zero index, the determinant identity makes the next value a unit; "
                    + "the addition identity then closes the zero indices under negation. "
                    + "Every additive subgroup of the integers is cyclic. Lean chooses "
                    + "a generator g using Classical.choose and takes its natural "
                    + "absolute value. In the display gZ denotes its subgroup of integer "
                    + "multiples. This construction is noncomputable and may give zero "
                    + "over an infinite ring; positivity is proved separately under "
                    + "the finite-ring hypothesis.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lucas_eq_zero_iff_entry_dvd", "Zero indices are exactly entry-point multiples",
                ZeroIndicesFormula(),
                "Membership in the cyclic subgroup is integer divisibility by its "
                    + "generator. Replacing that generator by its natural absolute value "
                    + "does not change divisibility. The equivalence includes negative "
                    + "indices and does not require a finite ring.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("entry_point_spec", "The least positive zero index over a finite ring",
                EntrySpecFormula(),
                "The companion unit has positive finite order, and its power at that "
                    + "order is the identity. Thus there is a positive zero index. The "
                    + "divisibility characterization makes e positive, makes e itself "
                    + "a zero index, and bounds it by every positive natural zero index. "
                    + "This identifies the subgroup construction with the usual entry "
                    + "point of the sequence at nonnegative indices.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lucas_even_descent", "Exactly one descent alternative in ZMod m",
                DescentFormula(),
                "The ring theorem gives 2U(n)=0 for arbitrary p. "
                    + "In ZMod m, the self-negative residues are zero and the half-modulus "
                    + "residue. In the nonzero case, e divides 2n but does not divide n. "
                    + "Writing 2n=e c forces c odd and e even, hence n=c(e/2). "
                    + "The conclusion records both the evenness of e and the odd integer "
                    + "multiplier, including when n is negative.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Paragraph(Text(
                "Here Xor(A,B) means (A and not B) or (B and not A), matching Lean's "
                    + "exclusive disjunction. The alternatives are mutually exclusive "
                    + "because an even positive m is at least 2 and 0 < m/2 < m. "
                    + "Consequently the half-modulus residue is not zero. Both alternatives "
                    + "actually occur: for p=2, q=1 and m=4 the recurrence gives U(n)=n "
                    + "modulo 4 and e=4. The index n=4 gives the zero alternative, while "
                    + "n=2 gives the half-modulus alternative with odd multiplier c=1; "
                    + "both indices satisfy the two doubling hypotheses.")),
            Node("conjecture_five_two", "Conjecture 5.2 with integer parameters",
                IntegerParametersFormula(),
                "For integers p and q, the hypothesis gcd(q,m)=1 supplies the canonical "
                    + "unit Q in ZMod m. In the display unit(q,m) abbreviates "
                    + "ZMod.unitOfIsCoprime q (Int.isCoprime_iff_gcd_eq_one.mpr hqm), "
                    + "where hqm is the displayed gcd hypothesis; its value is q modulo m. "
                    + "Thus Q^n specifies the modular meaning of q^n even at negative "
                    + "indices, without integer division. Applying lucas_even_descent "
                    + "proves the paper's conjecture under precisely the hypotheses "
                    + "displayed here. The parity hypothesis on p is retained for fidelity "
                    + "to the cited statement and is not used by the proof.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("lucas-even-descent-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula R() => F.Id("R");
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula ZMod() => Call("ZMod", M());
    private static Formula Units(Formula ring) => Call("Units", ring);
    private static Formula Val(Formula unit) => Call("val", unit);
    private static Formula Cast(Formula value, Formula type) => Call("Cast", value, type);
    private static Formula Half(Formula value) => Call("Div", value, D(2));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula U(Formula p, Formula q, Formula n) => Call("U", p, q, n);
    private static Formula E(Formula p, Formula q) => Call("e", p, q);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Even(Formula x) => Call("Even", x);
    private static Formula Positive(Formula x) => Seq(D(0), Sp, Lt, Sp, x);
    private static Formula RingContext() => Seq(
        Forall, Sp, Typed("R", Seq(F.Id("Type"), Star)), Sp,
        OpenBracket, Call("CommRing", R()), CloseBracket, Comma);
    private static Formula Parameters(Formula p, Formula q, Formula ring) => Seq(
        Forall, Sp, p, Colon, Sp, ring, Comma, Sp,
        q, Colon, Sp, Units(ring), Comma);
    private static Formula IntegerIndex() => Seq(Forall, Sp, Typed("n", Integers()), Comma);

    private static Formula Matrix(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("bmatrix")), a, Amp, b, RowBreak, c, Amp, d,
        End, Grp(F.Id("bmatrix")));

    private static Formula CompanionFormula()
    {
        Formula companion = Call("companion", P(), Q());
        Formula inverseQ = Val(Power(Q(), new Formula.Negate(D(1))));
        return Disp(new Formula.Aligned([
            RingContext(), Parameters(P(), Q(), R()),
            Seq(companion, Colon, Sp, Units(Call("Mat2", R())), Comma),
            Equal(Val(companion), Matrix(P(), new Formula.Negate(Val(Q())), D(1), D(0))),
            Equal(Val(Power(companion, new Formula.Negate(D(1)))),
                Matrix(D(0), D(1), new Formula.Negate(inverseQ), Mul(inverseQ, P()))),
        ]));
    }

    private static Formula LucasFormula() => Disp(new Formula.Aligned([
        RingContext(), Parameters(P(), Q(), R()), IntegerIndex(),
        Equal(U(P(), Q(), N()), new Formula.Subscript(
            Paren(Val(Power(Call("companion", P(), Q()), N()))), Seq(D(1), Comma, D(0)))),
    ]));

    private static Formula RecurrenceFormula() => Disp(new Formula.Aligned([
        RingContext(), Parameters(P(), Q(), R()),
        Seq(Equal(U(P(), Q(), D(0)), D(0)), Sp, Land, Sp,
            Equal(U(P(), Q(), D(1)), D(1)), Sp, Land),
        Seq(IntegerIndex(), Sp, Equal(U(P(), Q(), Add(N(), D(2))),
            Sub(Mul(P(), U(P(), Q(), Add(N(), D(1)))), Mul(Val(Q()), U(P(), Q(), N()))))),
    ]));

    private static Formula DoublingHypotheses(Formula p, Formula q) => Seq(
        Equal(U(p, q, Mul(D(2), N())), D(0)), Sp, Rightarrow, Sp,
        Equal(U(p, q, Add(Mul(D(2), N()), D(1))), Val(Power(q, N()))), Sp, Rightarrow);

    private static Formula TwoTorsionFormula() => Disp(new Formula.Aligned([
        RingContext(), Parameters(P(), Q(), R()), IntegerIndex(),
        DoublingHypotheses(P(), Q()),
        Equal(Mul(D(2), U(P(), Q(), N())), D(0)),
    ]));

    private static Formula EntryPointFormula() => Disp(new Formula.Aligned([
        RingContext(), Parameters(P(), Q(), R()),
        Seq(Typed("g", Integers()), Comma, Sp,
            F.Id("g"), Integers(), Sp, Eq, Sp,
            OpenBrace, Sp, Typed("n", Integers()), Sp, Mid, Sp,
            Equal(U(P(), Q(), N()), D(0)), Sp, CloseBrace, Comma),
        Seq(Equal(E(P(), Q()), Call("natAbs", F.Id("g"))), Sp, InMacro, Sp, Naturals()),
    ]));

    private static Formula ZeroIndicesFormula() => Disp(new Formula.Aligned([
        RingContext(), Parameters(P(), Q(), R()), IntegerIndex(),
        Seq(Equal(U(P(), Q(), N()), D(0)), Sp, Iff, Sp,
            Cast(E(P(), Q()), Integers()), Sp, Mid, Sp, N()),
    ]));

    private static Formula EntrySpecFormula() => Disp(new Formula.Aligned([
        RingContext(),
        Seq(Grp(), OpenBracket, Call("Finite", R()), CloseBracket, Comma),
        Parameters(P(), Q(), R()),
        Seq(Positive(E(P(), Q())), Sp, Land, Sp,
            Equal(U(P(), Q(), Cast(E(P(), Q()), Integers())), D(0)), Sp, Land),
        Seq(Forall, Sp, Typed("r", Naturals()), Comma, Sp,
            Positive(F.Id("r")), Sp, Rightarrow, Sp,
            Equal(U(P(), Q(), Cast(F.Id("r"), Integers())), D(0)), Sp, Rightarrow, Sp,
            E(P(), Q()), Sp, Leq, Sp, F.Id("r")),
    ]));

    private static Formula Alternatives(Formula p, Formula q) => Call("Xor",
        Equal(U(p, q, N()), D(0)),
        Seq(Equal(U(p, q, N()), Cast(Half(M()), ZMod())), Sp, Land, Sp,
            Even(E(p, q)), Sp, Land, Sp,
            Exists, Sp, Typed("c", Integers()), Comma, Sp,
            Call("Odd", F.Id("c")), Sp, Land, Sp,
            Equal(N(), Mul(F.Id("c"), Half(Cast(E(p, q), Integers()))))));

    private static Formula DescentFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, Typed("m", Naturals()), Comma, Sp,
            Positive(M()), Sp, Rightarrow, Sp, Even(M()), Sp, Rightarrow),
        Seq(Forall, Sp, Typed("p", ZMod()), Comma),
        Seq(Forall, Sp, Typed("q", Units(ZMod())), Comma, Sp, IntegerIndex()),
        DoublingHypotheses(P(), Q()),
        Alternatives(P(), Q()),
    ]));

    private static Formula IntegerParametersFormula()
    {
        Formula p = Cast(P(), ZMod());
        Formula q = F.Id("Q");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed("p", Integers()), Comma, Sp, Typed("q", Integers()), Comma, Sp,
                Typed("m", Naturals()), Comma),
            Seq(Positive(M()), Sp, Rightarrow, Sp, Even(P()), Sp, Rightarrow, Sp,
                Even(M()), Sp, Rightarrow, Sp,
                Equal(Call("gcd", Q(), Cast(M(), Integers())), D(1)), Sp, Rightarrow),
            IntegerIndex(),
            Seq(Named("let"), Sp, q, Colon, Sp, Units(ZMod()), Sp, Eq, Sp,
                Call("unit", Q(), M()), Sp, Named("in")),
            DoublingHypotheses(p, q),
            Alternatives(p, q),
        ]));
    }
}
