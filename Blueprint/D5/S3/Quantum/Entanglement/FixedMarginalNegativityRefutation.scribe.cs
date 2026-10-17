using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FixedMarginalNegativityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/QuantumChannels/baiochruscinskihorodeckimessinasarbicki2019fixedmarginals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At fixed two-qutrit marginals diag(49,47,4)/100 and diag(94,5,1)/100, a density matrix has greater negativity than the candidate of Baio, Chruscinski, Horodecki, Messina and Sarbicki.",
        H("The fixed-marginal candidate need not maximize two-qutrit negativity"),
        Blocks(
            Paragraph(Text(
                "The two factors are A and B, each with basis indexed by Fin 3 = {0,1,2}. "
                    + "Matrices act on their tensor product, with row and column indices in Fin 3 × Fin 3. "
                    + "The ket |ij⟩ is the basis vector |i⟩ ⊗ |j⟩, the dagger is conjugate transpose, "
                    + "and real coefficients of complex matrices are interpreted through the usual inclusion into C. "
                    + "All sums include every element of the indicated finite index set.")),
            Node("orderedMarginal", "The ordered fixed marginal",
                MarginalFormula("orderedMarginal", Subscript(F.Id("x"), D(1)), Subscript(F.Id("x"), D(2))),
                Blocks(Paragraph(Text(
                    "The two diagonal matrices ρ_A and ρ_B in Eq. (24) share this form, "
                        + "with parameters (λ₁, λ₂) for A and (μ₁, μ₂) for B. "
                        + "Its entries are 1 − x₁ − x₂, x₁ and x₂ in the basis order 0,1,2. "
                        + "This definition is made for all real parameters; "
                        + "the conjecture below imposes their ordering and positivity.")))),
            Node("candidate", "The candidate of Eq. (27)", CandidateFormula(),
                Blocks(Paragraph(Text(
                    "The vector φ has amplitudes √(1 − λ₁ − λ₂), √μ₁ and √μ₂ on |00⟩, |11⟩ and |22⟩. "
                        + "Its outer product, together with the two displayed diagonal terms, is Eq. (27) "
                        + "in the matrix form of Eq. (30). The square roots are real square roots, "
                        + "with value zero on negative inputs, so the formula also specifies the definition "
                        + "outside the parameter region used below.")))),
            Node("claim", "The maximizing conjecture in the region of Eq. (27)", ClaimFormula(), Blocks(
                Paragraph(Text("The negativity in this assertion is Eq. (4), "),
                    Math(In(NegativityFormula())), Text(
                        ", using the definition "),
                    Ref("D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.negativity"),
                    Text(" with both factors indexed by Fin 3.")),
                Paragraph(Text(
                    "The trace norm used here is the real part of the trace of the positive square root:"),
                    Math(In(TraceNormFormula())), Text(".")),
                Paragraph(Text(
                    "Partial transposition acts on B alone, exchanging the second row and column indices:"),
                    Math(In(PartialTransposeFormula())), Text(".")),
                Paragraph(Text(
                    "Section IV conjectures that the quasidistillable candidates maximize negativity at fixed marginals. "
                        + "Here this assertion is restricted to the region of Eq. (27): the two spectra are "
                        + "nonnegative and in decreasing order, μ₁ + μ₂ ≤ λ₁ + λ₂, μ₁ < λ₁ and μ₂ < λ₂. "
                        + "Every density matrix with the two prescribed marginals is asserted to have negativity "
                        + "at most that of the candidate. The condition R ≥ 0 means complex Hermitian "
                        + "positive semidefiniteness, and Tr(R) = 1 supplies normalization.")),
                Paragraph(Text("The two partial traces in the assertion are specified entrywise by "),
                    Math(In(PartialTraceFormula("B"))), Text(" and "),
                    Math(In(PartialTraceFormula("A"))), Text(
                        ". Thus Tr_B removes the second factor and Tr_A removes the first.")))),
            Describe.Lean(
                DescribeId.Create("fixed-marginal-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A state with the same marginals has strictly greater negativity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take λ = (47,4)/100 and μ = (5,1)/100. Then ρ_A = diag(49,47,4)/100 "
                            + "and ρ_B = diag(94,5,1)/100 satisfy every parameter inequality above. "
                            + "Let χ = (7|00⟩ + |12⟩ + 2|21⟩)/10 and set "
                            + "ρ = (99/100)(χχ† + (45/100)|10⟩⟨10| + (1/100)|11⟩⟨11|) "
                            + "+ (1/100)ρ_A ⊗ ρ_B. Each summand is positive semidefinite, "
                            + "the total trace is one, and the partial traces are ρ_A and ρ_B.")),
                    Paragraph(Text(
                        "For a vector v write O(v) = vv†. Define "
                            + "𝑲 = O(|01⟩ − |20⟩)/2 + O(7|02⟩ − |10⟩)/50 "
                            + "+ O(|11⟩ − |22⟩)/2. These three rank-one terms are mutually orthogonal "
                            + "projections, so 𝑲† = 𝑲 and 𝑲² = 𝑲. The reflection 1 − 2𝑲 is unitary "
                            + "and Tr((1 − 2𝑲)ρ^Γ) = 1 + 2·8168881/50000000. "
                            + "The variational characterization of the trace norm therefore gives "
                            + "N(ρ) ≥ 8168881/50000000 > 7/50.")),
                    Paragraph(Text(
                        "Let σ be the candidate at these parameters, so "
                            + "σ = φφ† + (42/100)|10⟩⟨10| + (3/100)|20⟩⟨20| "
                            + "with φ = (7|00⟩ + √5|11⟩ + |22⟩)/10. Its partial transpose is P − Q, where "
                            + "P = (49/100)|00⟩⟨00| + (5/100)|11⟩⟨11| + (1/100)|22⟩⟨22| "
                            + "+ O(35|01⟩ + 47√5|10⟩)/26000 "
                            + "+ O(35|02⟩ + 43|20⟩)/35500 "
                            + "+ (√5/200)O(|12⟩ + |21⟩), and "
                            + "Q = O(7|01⟩ − √5|10⟩)/1040 "
                            + "+ O(35|02⟩ − 28|20⟩)/35500 "
                            + "+ (√5/200)O(|12⟩ − |21⟩). Both P and Q are positive semidefinite. "
                            + "Their traces are 1 + 100159/923000 + √5/100 and 100159/923000 + √5/100. "
                            + "The trace-norm triangle inequality yields "
                            + "N(σ) ≤ 100159/923000 + √5/100 < 7/50, using √5 < 5/2. "
                            + "Hence N(σ) < N(ρ) although their marginals agree, contradicting the conjecture. "
                            + "The coherences of χ join |00⟩, |12⟩ and |21⟩, rather than the three "
                            + "equally indexed basis vectors used by the candidate."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baio-chruscinski-horodecki-messina-sarbicki-2019-fixed-marginal-negativity-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, BlockSequence prose) =>
        Describe.Lean(DescribeId.Create("fixed-marginal-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            prose, DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula EqualTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula PlusOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula MinusOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula TimesOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Subscript(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Pair(Formula first, Formula second) => Parenthesized(Seq(first, Comma, Sp, second));
    private static Formula FinThree => LocalCall("Fin", D(3));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Indices => Parenthesized(Seq(FinThree, Sp, F.Times, Sp, FinThree));
    private static Formula Matrices => LocalCall("Matrix", Indices, Indices, Complexes);
    private static Formula L1 => Subscript(LambdaLower, D(1));
    private static Formula L2 => Subscript(LambdaLower, D(2));
    private static Formula M1 => Subscript(Mu, D(1));
    private static Formula M2 => Subscript(Mu, D(2));
    private static Formula Remaining(Formula first, Formula second) => MinusOf(MinusOf(D(1), first), second);
    private static Formula Parameters(Formula body) => All(L1, Reals, All(L2, Reals, All(M1, Reals, All(M2, Reals, body))));
    private static Formula Adjoint(Formula value) => new Formula.Power(value, Named("dagger"));
    private static Formula Partial(Formula value) => new Formula.Power(value, Gamma);
    private static Formula Trace(Formula value) => LocalCall("Tr", value);
    private static Formula TraceNorm(Formula value) => Subscript(new Formula.Norm(value), D(1));
    private static Formula SquareRoot(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Ket(byte first, byte second) => Seq(Bar, D(first), D(second), Rangle);
    private static Formula Outer(Formula vector) => TimesOf(Parenthesized(vector), Adjoint(Parenthesized(vector)));
    private static Formula BasisProjection(byte first, byte second) => Outer(Ket(first, second));
    private static Formula PartialTrace(string factor, Formula value) => At(Subscript(Named("Tr"), F.Id(factor)), value);
    private static Formula SumOver(Formula variable, Formula body) =>
        Seq(Subscript(Sum, Typed(variable, FinThree)), Sp, Parenthesized(body));

    private static Formula NegativityFormula()
    {
        var r = F.Id("R");
        return All(r, Matrices, EqualTo(LocalCall("negativity", r),
            Fraction(MinusOf(TraceNorm(Partial(r)), D(1)), D(2))));
    }

    private static Formula TraceNormFormula()
    {
        var x = F.Id("X");
        return All(x, Matrices, EqualTo(TraceNorm(x),
            At(Re, Trace(SquareRoot(TimesOf(Adjoint(x), x))))));
    }

    private static Formula PartialTransposeFormula()
    {
        var r = F.Id("R");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var l = F.Id("l");
        var entries = EqualTo(At(Partial(r), Pair(i, j), Pair(k, l)), At(r, Pair(i, l), Pair(k, j)));
        return All(r, Matrices, All(i, FinThree, All(j, FinThree, All(k, FinThree, All(l, FinThree, entries)))));
    }

    private static Formula MarginalFormula(string name, Formula first, Formula second) =>
        All(first, Reals, All(second, Reals, EqualTo(LocalCall(name, first, second),
            Seq(Begin, Grp(F.Id("pmatrix")),
                Remaining(first, second), Amp, D(0), Amp, D(0), RowBreak,
                D(0), Amp, first, Amp, D(0), RowBreak,
                D(0), Amp, D(0), Amp, second,
                End, Grp(F.Id("pmatrix"))))));

    private static Formula CandidateFormula()
    {
        var vector = PlusOf(PlusOf(TimesOf(SquareRoot(Remaining(L1, L2)), Ket(0, 0)),
            TimesOf(SquareRoot(M1), Ket(1, 1))), TimesOf(SquareRoot(M2), Ket(2, 2)));
        var state = PlusOf(PlusOf(Outer(Varphi),
            TimesOf(Parenthesized(MinusOf(L1, M1)), BasisProjection(1, 0))),
            TimesOf(Parenthesized(MinusOf(L2, M2)), BasisProjection(2, 0)));
        return Parameters(Seq(Named("let"), Sp, Varphi, Sp, F.Eq, Sp, vector, Sp, Named("in"), Sp,
            EqualTo(LocalCall("candidate", L1, L2, M1, M2), state)));
    }

    private static Formula PartialTraceFormula(string factor)
    {
        var r = F.Id("R");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var entry = factor == "B" ? At(r, Pair(i, j), Pair(k, j)) : At(r, Pair(j, i), Pair(j, k));
        return All(r, Matrices, All(i, FinThree, All(k, FinThree,
            EqualTo(At(PartialTrace(factor, r), i, k), SumOver(j, entry)))));
    }

    private static Formula ClaimFormula()
    {
        var r = F.Id("R");
        var conclusion = LeTo(LocalCall("negativity", r), LocalCall("negativity", LocalCall("candidate", L1, L2, M1, M2)));
        var states = All(r, Matrices, Imp(And(LeTo(D(0), r), EqualTo(Trace(r), D(1))),
            Imp(EqualTo(PartialTrace("B", r), LocalCall("orderedMarginal", L1, L2)),
                Imp(EqualTo(PartialTrace("A", r), LocalCall("orderedMarginal", M1, M2)), conclusion))));
        return IffOf(Named("claim"), Parameters(
            Imp(LeTo(L2, L1), Imp(LeTo(L1, Remaining(L1, L2)), Imp(LeTo(D(0), L2),
            Imp(LeTo(M2, M1), Imp(LeTo(M1, Remaining(M1, M2)), Imp(LeTo(D(0), M2),
            Imp(LeTo(PlusOf(M1, M2), PlusOf(L1, L2)), Imp(LtTo(M1, L1), Imp(LtTo(M2, L2), states)))))))))));
    }
}
