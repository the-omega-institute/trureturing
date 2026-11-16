using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Cyclic;

internal sealed class HalfOrderSynchronizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var i = X("I"); var g = X("G"); var epsilon = X("epsilon"); var j = X("i");
        Formula Context(Formula f)
        {
            f = Imp(All("i", i, Equal(C("orderOf", C("epsilon", j)), Num(2))), f);
            f = All("epsilon", C("Pi", i, g), f);
            f = Instances(All("i", i, C("IsCyclic", C("G", j))), f);
            f = Instances(All("i", i, C("Fintype", C("G", j))), f);
            f = Instances(All("i", i, C("Group", C("G", j))), f);
            f = All("G", new Formula.TypeArrow(i, X("Typev")), f);
            f = Instances(C("Nonempty", i), f);
            f = Instances(C("Fintype", i), f);
            return All("I", X("Typeu"), f);
        }
        var count = new Formula.Relation(
            Multiply(C("card", C("B", g, epsilon)),
                new Formula.Power(Num(2), new Formula.Binary(C("card", i), FormulaBinaryOperator.Subtract, Num(1)))),
            FormulaRelationOperator.LessThanOrEqual, C("card", C("Pi", i, g)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual half-order failure event in a nonempty finite family of cyclic groups has at most one part in two to the number of non-anchor coordinates.",
            H("Half-order failure in finite cyclic products"),
            Blocks(
                Paragraph(Text("Let I be a nonempty finite index type and let G(i) be finite cyclic groups, with possibly different sizes. Choose epsilon(i) of order two. Write P for the dependent product of the G(i), k for card(I), and B(G,epsilon) for the subtype of x in P satisfying NOT(Even(orderOf(x)) AND x^(orderOf(x)/2) unequal to epsilon). All group elements are included, in particular the identity and elements of odd order. The product P is not required to be cyclic.")),
                Describe.Lean(DescribeId.Create("half-order-failure-count"),
                    DeclarationHandle.Create("D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization.failure_count_le"),
                    H("The all-family failure count"), StatementSource.FromAuthor(Disp(Context(count))),
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/shor1997gateorbits")),
                    Blocks(
                        Paragraph(Text("In a cyclic factor epsilon is the unique element of order two. If d=orderOf(x) divides an even positive M, the local half-power x^(M/2) equals epsilon exactly when d.factorization(2)=M.factorization(2). Indeed its square is one; its being one is equivalent to d dividing M/2, or to 2*d dividing M, which is equivalent to strict inequality between the binary order valuations. For the product, Pi.orderOf and Finset.factorization_lcm express its binary order valuation as the maximum of the local valuations. Thus failure is exactly synchronization of every local valuation. If the product order is odd all the valuations are zero, so this case is retained.")),
                        Paragraph(Text("Choose a full-order generator g(i) in each factor. Raising multiplication by g(i) to card(G(i))/2 multiplies the resulting half-power by epsilon(i), interchanging one and epsilon(i). The local half-power criterion therefore shows that multiplying any element by g(i) changes the binary valuation of its order. This argument applies to every even cyclic size and does not assign a finite binary valuation to the exponent zero.")),
                        Paragraph(Text("Fix an anchor a in I. Encode a failing tuple x together with one Boolean b(i) for each i unequal to a by retaining x(a) and replacing x(i) by x(i)*g(i) exactly when b(i) is true. The anchor gives the common valuation t of the original tuple. In each other coordinate the encoded valuation equals t exactly when its bit is false, so equal encodings have equal bits. Cancellation of the generators then recovers the original tuples. This constructs an injection from B times the Boolean functions on I without a into the actual product P. The Boolean function type has cardinality 2^(k-1), giving the stated count. For k=1 there are no bits and every tuple fails; the inequality is equality.")),
                        Paragraph(Text("The count is the classical common-valuation estimate of Shor, Section 5, PDF page 16. Its proof counts one fixed actual product, including heterogeneous cyclic sizes, rather than combining separately optimal fibers. It makes no assertion of mathematical novelty."))),
                    DescribeRole.Theorem),
                Paragraph(Text("For odd N greater than one, put I=N.primeFactors and G(p)=(ZMod(p^(N.factorization(p)))) units. Every exponent is positive; each p is odd. ZMod.isCyclic_units_of_prime_pow supplies cyclicity, and the literal unit -1 has order two. The equivalence Units.mapEquiv((ZMod.equivPi N hN).toMulEquiv), followed by MulEquiv.piUnits, preserves order, natural powers, and literal -1. It therefore identifies the same literal Good(u) event, Even(orderOf(u)) and u^(orderOf(u)/2) unequal to -1, with the product event above. Its restriction is a bijection of failure subtypes, so Nat.card_congr transports the count without changing the uniform unit carrier.")),
                Paragraph(Text("Let T=card((ZMod N) units), F be its failure count, S its Good count, and q=2^(k-1). The transported estimate is F*q at most T. Since the unit carrier contains one, T is positive; q is positive, and S+F=T. Division in the real or rational numbers gives S/T at least 1-1/q. The pinned isPrimePow_iff_card_primeFactors_eq_one and nonemptiness of N.primeFactors imply k at least two when N is not a prime power. Then q is at least two and S/T is at least one half. All units, including one, are sampled uniformly; no independent latent probability law is assumed.")),
                Paragraph(Text("The deterministic factor implication applies to every natural N greater than two, including even N. For any natural a with Nat.Coprime a N, put u=ZMod.unitOfCoprime a hcop, r=orderOf(u), and m=r/2. Coprimality and N greater than two imply a at least one, so x=a^m is at least one. The finite unit group gives r positive; if r is even then zero is less than m and m is less than r. The pinned pow_ne_one_of_lt_orderOf rules out u^m=1, and Good(u) rules out u^m=-1. Also (u^m)^2=1 by pow_orderOf_eq_one and Nat.div_mul_cancel. These are statements about the true order, not an arbitrary even period.")),
                Paragraph(Text("The coercion ZMod.coe_unitOfCoprime identifies the residue of the original natural power x with u^m. Since x is at least one, Nat.cast_sub gives the residue of the natural subtraction x-1 as the ring difference. Factoring x squared minus one gives N dividing the natural product (x-1)*(x+1), by ZMod.natCast_eq_zero_iff. Neither factor is divisible by N, since their residues would force u^m=1 or u^m=-1. If gcd(x-1,N)=1, Nat.Coprime.dvd_of_dvd_mul_left forces N to divide x+1; if gcd(x+1,N)=1, Nat.Coprime.dvd_of_dvd_mul_right forces N to divide x-1. Both are contradictions. Nat.gcd_pos_of_pos_right and Nat.gcd_le_right therefore give, simultaneously, 1<gcd(x-1,N)<N and 1<gcd(x+1,N)<N. Nat.gcd_dvd_right shows each gcd divides N. No prime-power square-root classification or oddness hypothesis is used in this deterministic argument.")),
                Paragraph(Text("For an arbitrary actual unit u, let b=(u:ZMod N).val and t=((u^m):ZMod N).val. ZMod.val_coe_unit_coprime shows that b and t are coprime to N, hence positive. Every natural a representing u is also coprime to N by ZMod.isUnit_iff_coprime, hence positive. ZMod.natCast_zmod_val and the power coercion give a^m congruent to t and b^m congruent to t modulo N; they do not give natural equality with t. Nat.ModEq.sub uses the explicit bounds one at most a^m, b^m and t to transport subtraction of one. Addition transports directly. Nat.ModEq.gcd_eq then proves equality of the original-power, canonical-base-power and canonical-half-power gcd pairs. Thus both proper-divisor certificates hold for all positive representatives of the same actual unit. The identity remains in the sampling carrier, with Good(1) false because its order is one.")),
                Paragraph(Text("Define C(u) by adjoining to this same literal Good(u) event the simultaneous proper-divisor certificates for b^m and t, and for a^m for every natural representative a of u. The deterministic implication proves Good(u) implies C(u), while projection proves C(u) implies Good(u). Equiv.subtypeEquiv for the identity equivalence gives a bijection of these success subtypes; Nat.card_congr makes their counts equal. Consequently the uniform probability of C is exactly S/T and obeys the same bound 1-1/2^(k-1), and at least one half for odd non-prime-power N. Every local prime-power exponent remains N.factorization(p), with no restriction to squarefree N. The certificate is adjoined before transporting the estimate; it is not a claim about a different success event.")),
                Paragraph(Text("This is an application of the existing finite-group count and the pinned order, cancellation and congruence facts. It supplies the classical uniform-unit success bound together with both gcd factors on the same event. It does not supply hardware, complexity, quantum sampling, repeated-sample independence or a complete implementation of recursive prime factorization. The unit sampling law remains distinct from the counting-register distribution.")))));
    }
    private static Formula X(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula All(string s, Formula t, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Instances(Formula t, Formula f) => Seq(OpenBracket, t, CloseBracket, Sp, f);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
