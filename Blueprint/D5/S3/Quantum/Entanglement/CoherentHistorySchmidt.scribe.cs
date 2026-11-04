using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class CoherentHistorySchmidtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-occupation word states have exact cut ranks and positive binomial Schmidt weights.",
        H("Coherent History Schmidt Rank"),
        Blocks(
            Paragraph(Text(
                "A is any finite alphabet with decidable equality. Words are functions Fin n to A; "
                + "a is the total occupation multiset, and card(a)=t+s specifies the cut. "
                + "B(a,t) denotes Boundary(a,t), the finite type of multisets b with b<=a and "
                + "card(b)=t. val forgets this subtype. M(n,b) counts the actual words of length n "
                + "with occupation b. V(n,b,w) is their normalized uniform vector, evaluated at w. "
                + "C(a,t,s) denotes coefficientMatrix over the complex numbers. Matrix.rank is "
                + "the complex dimension of the range of its multiplication linear map. "
                + "This supplies the decomposition and rank clauses of the coherent-history atom; "
                + "its fixed-register pure-state circuit clause remains open.")),
            Describe.Lean(DescribeId.Create("history-legal-boundary"), DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.legal_iff"),
                H("Legal concatenations select a feasible occupation boundary"),
                StatementSource.FromAuthor(Disp(LegalBoundaryFormula)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/raveh2024dicke")),
                Blocks(Paragraph(Text(
                    "A concatenation has total occupation a exactly when its prefix occupation "
                    + "is a feasible boundary and its suffix occupation is the complementary multiset.")))),
            Theorem("history-word-state", "coefficient_eq_uniform_word", "Coefficients come from the full uniform word state",
                Parameters(All("u", Word(t), All("v", Word(s),
                    Eq(Call("C", a, t, s, u, v), V(Add(t, s), a, Call("FinAppend", u, v)))))),
                "Thus the coefficient is 1/sqrt(M(t+s,a)) exactly on legal concatenations, "
                + "and zero otherwise. The full word vector has norm one when card(a)=t+s."),
            Theorem("history-sector-factorization", "coefficient_factorization", "The matrix factors through feasible sectors",
                Parameters(Eq(C, Mul(Call("prefixIncidence", a, t), Call("suffixAmplitude", a, t, s)))),
                "The prefix incidence is one exactly when occupation(u)=val(b). The suffix "
                + "amplitude is 1/sqrt(M(t+s,a)) exactly when occupation(v)=a-val(b). "
                + "Both are zero elsewhere. This factorization bounds rank by the sector count."),
            Theorem("history-diagonal-restriction", "coefficient_diagonal_restriction", "Actual representative words give a full diagonal restriction",
                Parameters(All("h", Length, Eq(Call("submatrix", C, Call("prefixRepresentative", a, t),
                    Call("suffixRepresentative", Id("h"))),
                    Call("diagonal", Seq(Id("b"), Colon, B, Sp, Mapsto, Sp,
                        Call("historyAmplitude", a, Add(t, s))))))),
                "Each row and column is chosen by listing its prescribed occupation. The restriction "
                + "is diagonal with the nonzero full-history amplitude on every diagonal entry. "
                + "Its rank supplies the lower bound for the full coefficient matrix."),
            Theorem("history-coefficient-rank", "coefficient_rank", "Every cut rank equals the feasible boundary count",
                Parameters(Imp(Length, Eq(Call("rank", C), Call("card", Call("boundaries", a, t))))),
                "The theorem concerns the entire rectangular word matrix. In particular t=0 "
                + "and s=0 are allowed. Setting s=card(a)-t yields every valid cut."),
            Theorem("history-positive-coefficients", "schmidt_coefficient_pos", "Every Schmidt coefficient is positive",
                Parameters(Imp(Length, All("b", B, Lt(D(0), Coefficient)))),
                "The coefficient is sqrt(M(t,val(b))) times sqrt(M(s,a-val(b))) divided by "
                + "sqrt(M(t+s,a)). All three word fibers contain explicitly constructed representatives."),
            Theorem("history-squared-coefficients", "schmidt_coefficient_sq", "Squared coefficients are multiplicity ratios",
                Parameters(All("b", B, Eq(new Formula.Power(Coefficient, D(2)),
                    new Formula.Fraction(Mul(M(t, Val(b)), M(s, Complement(b))), M(Add(t, s), a))))),
                "The displayed multiplicities are actual finite word-fiber cardinalities. "
                + "The following binomial identity uses their universal multinomial counting formula."),
            Theorem("history-binomial-weights", "schmidt_coefficient_sq_binomial", "Squared coefficients are binomial weights",
                Parameters(Imp(Length, All("b", B,
                    Eq(new Formula.Power(Coefficient, D(2)), BinomialWeight)))),
                "Each coordinate binomial coefficient and the denominator are natural numbers "
                + "canonically included in the reals. The product runs over every symbol in A, "
                + "including zero occupation coordinates. The proof uses actual prefix, suffix, "
                + "and full word cardinalities and cancels positive factorial products. "
                + "No counting identity is assumed, and both endpoint cuts are included."),
            Theorem("history-binomial-coefficients", "schmidt_coefficient_eq_sqrt_binomial", "The Schmidt coefficient is the positive square root",
                Parameters(Imp(Length, All("b", B, Eq(Coefficient, Call("sqrt", BinomialWeight))))),
                "sqrt is the nonnegative real square root. Positivity of the existing coefficient "
                + "selects that root, identifying the coefficient in the normalized decomposition."),
            Theorem("history-normalized-decomposition", "normalized_coefficient_factorization", "Normalized occupation-sector decomposition",
                Parameters(Imp(Length, All("u", Word(t), All("v", Word(s),
                    Eq(Call("C", a, t, s, u, v), SumAt("b", B,
                        Mul(Mul(Call("ofReal", Coefficient), V(t, Val(b), u)), V(s, Complement(b), v)))))))),
                "The equality is coordinatewise on every actual prefix and suffix word. ofReal "
                + "is the canonical inclusion of the real positive coefficient into the complex numbers."),
            Theorem("history-two-gram-identities", "cut_sector_gram", "Both sides are orthonormal",
                Parameters(Imp(Length, All("b", B, All("c", B,
                    And(Eq(SumAt("u", Word(t), Mul(Call("star", V(t, Val(b), u)),
                            V(t, Val(c), u))), Delta),
                        Eq(SumAt("v", Word(s), Mul(Call("star", V(s, Complement(b), v)),
                            V(s, Complement(c), v))), Delta)))))),
                "The diagonal Gram entries are one and the off-diagonal entries are zero. "
                + "Distinct prefix occupations have distinct complementary suffix occupations."),
            Theorem("history-boundary-maximum", "boundaryMaximum", "Maximum actual boundary size",
                DiscreteOccupation(Eq(Call("boundaryMaximum", a),
                    SupAt(Add(Call("card", a), D(1)), Call("card", Call("boundaries", a, t))))),
                "The finite supremum ranges over every natural t in range(card(a)+1), "
                + "including zero and the full cut. It is a maximum of actual cardinalities.",
                DescribeRole.Definition),
            Theorem("history-general-maximum-rank", "history_max_schmidt_rank", "Maximum Schmidt rank is the maximum actual boundary size",
                GeneralOccupation(Eq(SupAt(Add(Call("card", a), D(1)),
                    Call("rank", Call("C", a, t, Sub(Call("card", a), t)))), Call("boundaryMaximum", a))),
                "Every cut in the finite supremum satisfies t<=card(a), so the general rank theorem applies."),
            Paragraph(Text(
                "For the concrete statements, ast denotes occupation5040 on Option(Fin(3)), "
                + "constructed as capacityOccupation(4,tailCapacities5040) with tail capacities "
                + "(2,1,1). none is the count-four symbol; some(0), some(1), some(2) have counts "
                + "two, one, one. rankAt(t) is rank(C(ast,t,8-t)), on actual words. r(t) denotes "
                + "the landed timeSlice5040Count. The sequence below is transported from its "
                + "existing theorem through the generic bounded-coordinate equivalence.")),
            Theorem("history-occupation-5040", "occupation5040", "The actual occupation for 5040",
                Eq(Ast, Call("capacityOccupation", D(4), Id("tailCapacities"))),
                "tailCapacities is BoundedTimeSlice.tailCapacities5040 on Fin(3), namely (2,1,1).",
                DescribeRole.Definition),
            Theorem("history-occupation-5040-card", "occupation_5040_card", "Eight actual time slots",
                Eq(Call("card", Ast), D(8)),
                "The generic capacity cardinality and landed tail sum give the actual multiset length."),
            Theorem("history-5040-rank-transport", "history_5040_rank_eq_sliceCount", "Actual history rank equals the landed slice count",
                All("t", N, Imp(Le(t, D(8)), Eq(RankAt(t), Call("r", t)))),
                "The rank of the full coefficient matrix is its actual boundary count; the "
                + "bounded-coordinate equivalence identifies that count with r(t)."),
            Theorem("history-5040-rank-sequence", "history_5040_rank_sequence", "The nine actual cut ranks",
                Eq(Call("map", Seq(t, Sp, Mapsto, Sp, RankAt(t)), Call("ListRange", D(9))),
                    Call("List", D(1), D(4), D(8), D(1, 1), D(1, 2), D(1, 1), D(8), D(4), D(1))),
                "ListRange(9) lists zero through eight. No independent rank or boundary enumeration is used."),
            Theorem("history-5040-rank-maximum-cut", "history_5040_rank_bound", "Every valid cut is bounded, with equality only at four",
                All("t", N, Imp(Le(t, D(8)),
                    And(Le(RankAt(t), D(1, 2)), Iff(Eq(RankAt(t), D(1, 2)), Eq(t, D(4)))))),
                "This consumes the landed unique maximum through the actual-rank transport."),
            Theorem("history-5040-boundary-maximum", "occupation_5040_boundary_maximum", "The actual maximum boundary size is twelve",
                Eq(Call("boundaryMaximum", Ast), D(1, 2)),
                "The universal landed bound controls the supremum, and the actual cut four attains it."),
            Theorem("history-5040-maximum-schmidt-rank", "history_5040_max_schmidt_rank", "Maximum Schmidt rank twelve is attained at four",
                And(Eq(SupAt(D(9), RankAt(t)), D(1, 2)),
                    Eq(Call("rank", Call("C", Ast, D(4), D(4))), D(1, 2))),
                "This is the maximum of the actual coefficient-matrix ranks of the eight-slot "
                + "uniform occupation history, with an explicit attaining cut."))));

    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Quantum/Entanglement/CoherentHistorySchmidt." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/raveh2024dicke")),
            Blocks(Paragraph(Text(text))), role);

    private static Formula LegalBoundaryFormula
    {
        get
        {
            var feasible = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("b"), Call("Boundary", a, t),
                And(Eq(Call("occupation", u), Val(b)), Eq(Call("occupation", v), Complement(b))));
            var appended = new Formula.Apply(Seq(Operatorname, Grp(Id("Fin"), Dot, Id("append"))), [u, v]);
            return DiscreteOccupation(All("t", N, All("s", N, All("u", Word(t), All("v", Word(s),
                Iff(Eq(Call("occupation", appended), a), feasible))))));
        }
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula a => Id("a");
    private static Formula b => Id("b");
    private static Formula c => Id("c");
    private static Formula t => Id("t");
    private static Formula s => Id("s");
    private static Formula u => Id("u");
    private static Formula v => Id("v");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula B => Call("B", a, t);
    private static Formula C => Call("C", a, t, s);
    private static Formula Ast => Id("ast");
    private static Formula RankAt(Formula time) => Call("rank", Call("C", Ast, time, Sub(D(8), time)));
    private static Formula SupAt(Formula limit, Formula body) =>
        Call("FinsetSup", Call("range", limit), Seq(t, Sp, Mapsto, Sp, body));
    private static Formula GeneralOccupation(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A"))),
            All("a", Call("Multiset", Id("A")), body)));
    private static Formula DiscreteOccupation(Formula body) => All("A", Id("Type"),
        Imp(Call("DecidableEq", Id("A")), All("a", Call("Multiset", Id("A")), body)));
    private static Formula Length => Eq(Call("card", a), Add(t, s));
    private static Formula Coefficient => Call("schmidtCoefficient", a, t, s, b);
    private static Formula BinomialWeight => new Formula.Fraction(
        ProdAt("z", Id("A"), Call("choose", Call("count", a, Id("z")),
            Call("count", Val(b), Id("z")))), Call("choose", Add(t, s), t));
    private static Formula Delta => Call("ite", Eq(b, c), D(1), D(0));
    private static Formula Word(Formula length) => Call("Word", Id("A"), length);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Complement(Formula x) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, Val(x));
    private static Formula M(Formula length, Formula x) => Call("M", length, x);
    private static Formula V(Formula length, Formula x, Formula word) => Call("V", length, x, word);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parameters(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A"))),
            All("a", Call("Multiset", Id("A")), All("t", N, All("s", N, body)))));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula SumAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula ProdAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(Id(name), Colon, domain)), Grp(body));
}
