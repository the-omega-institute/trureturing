using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class LatticeLindbladianZeroSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/klausen2025spectragenerators");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-range translation-invariant lattice Lindblad matrices define a bounded operator with spectral zero.",
        H("Spectral zero for a lattice Lindblad generator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-range"),
                DeclarationHandle.Create(Module + ".IsFiniteRange"),
                H("Finite matrix range"),
                StatementSource.FromAuthor(Disp(FiniteRangeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Hamiltonian matrix h vanishes beyond distance r from its diagonal. "
                    + "The jump matrix indexed by k vanishes unless both its row and column lie within distance r of k. "
                    + "The radius is a natural number, included in the integers before comparison with distances. "
                    + "These are the matrix support conditions associated with (Finite Range) in section02.tex, line 41. "
                    + "The Hamiltonian condition is expressed using the distance between its own two indices; "
                    + "it has no jump index k. No symmetry or rank condition is part of this predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("translation-invariant"),
                DeclarationHandle.Create(Module + ".IsTranslationInvariant"),
                H("Translation of matrix indices"),
                StatementSource.FromAuthor(Disp(TranslationFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Translating both indices of h by one leaves its entries unchanged. "
                    + "Translating the jump index and both matrix indices by one likewise leaves the jump entries unchanged. "
                    + "This is the matrix form of (TransInv) in section02.tex, line 42; "
                    + "iteration gives the corresponding identities for every integer translation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lindblad-entry"),
                DeclarationHandle.Create(Module + ".lindbladEntry"),
                H("The generator in matrix elements"),
                StatementSource.FromAuthor(Disp(EntryFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an arbitrary complex kernel ρ, this expression is the (x,y) entry of the commutator term "
                    + "and the jump gain minus the two half anticommutator terms. "
                    + "The operation star on a complex entry is complex conjugation. "
                    + "Every sum is an unconditional sum over the integers; finite range makes the relevant sums finite. "
                    + "The real parameter g is included in the complex numbers and multiplies the entire dissipative term. "
                    + "The Lindblad expression appears in section02.tex, lines 6–13; "
                    + "the effective Hamiltonian there at line 22 and its use in section03.tex, lines 179–182, "
                    + "specify the placement of the coupling constant. "
                    + "The definition allows every real g and does not impose positivity or self-adjointness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A bounded generator with zero in its spectrum"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The space ObserverHilbertSpace on the integer pairs is the complex square-summable kernel space. "
                        + "The vectorization in section03.tex, lines 162–165, identifies this space with the Hilbert–Schmidt operators "
                        + "on the square-summable sequences on the integers. "
                        + "The spectrum here is the complex spectrum in the unital algebra of continuous complex linear endomorphisms. "
                        + "The question in section04.tex, line 574, asks for spectral zero under finite range, translation invariance "
                        + "and rank one. The statement holds for every real g, without a rank or self-adjointness assumption.")),
                    Paragraph(Text(
                        "First, translation invariance writes h(x,y) as h(0,y−x) and ℓ(k,x,y) as ℓ(0,x−k,y−k). "
                        + "Only finitely many differences survive the support conditions, so all matrix entries have a common norm bound. "
                        + "Replacing the unconditional sums by sums on the corresponding finite integer intervals makes each output entry "
                        + "a linear function of ρ. It depends only on ρ(u,v) with |u−x| and |v−y| at most 2r. "
                        + "Expanding this finite rectangle in its matrix units gives a finite sum over displacements w in [−2r,2r]²: "
                        + "each summand multiplies the translated value ρ(p+w) by the generator's entry on the matrix unit at p+w, evaluated at p. "
                        + "The entrywise bounds give a common nonnegative real bound m for these multiplying functions. "
                        + "Each translated multiplication operator is bounded: translation is an isometry and multiplication has norm at most m. "
                        + "Their finite sum is therefore a continuous complex linear operator t with exactly the required entries.")),
                    Paragraph(Text(
                        "Next let Pₙ be the kernel equal to one on (x,x) for −n ≤ x ≤ n and zero elsewhere. "
                        + "Its inner product with ρ is the sum of the diagonal entries of ρ on that interval, "
                        + "and its squared norm is 2n+1. "
                        + "For a matrix unit at q=(u,v), locality confines the output to |u−x| ≤ 2r and |v−y| ≤ 2r. "
                        + "The full sum of its diagonal output entries is zero. "
                        + "Indeed, the two commutator contributions cancel; for each jump index, "
                        + "the gain sum equals the sum of the conjugate product, while each loss contributes half of that same sum. "
                        + "All exchanges of sums are finite, with diagonal indices in [min(u,v)−2r,max(u,v)+2r] "
                        + "and jump indices in [u−r,u+r] union [v−r,v+r].")),
                    Paragraph(Text(
                        "For a fixed n, denote by κ(q) the sum of the diagonal output of the matrix unit at q over [−n,n]. "
                        + "At most 4r+1 diagonal entries contribute, so |κ(q)| ≤ (4r+1)m. "
                        + "Moreover κ(q) vanishes unless u lies in [n−2r,n+2r] union [−n−2r,−n+2r] "
                        + "and |v−u| ≤ 4r. If the two input indices are farther apart, locality gives zero; "
                        + "if u is outside the enlarged interval, there is no contribution; "
                        + "if u is strictly inside away from its ends, the restricted diagonal sum is the full zero sum. "
                        + "The remaining pairs number at most c=2(4r+1)(8r+1), independently of n. "
                        + "Expand an arbitrary ρ on the finite square [−n−2r,n+2r]² and exchange the finite sums. "
                        + "Only these boundary pairs remain. Since each |ρ(q)| is at most its square-summable norm, "
                        + "the triangle inequality gives |⟨Pₙ,tρ⟩| ≤ k‖ρ‖ with k=c(4r+1)m, uniformly in n.")),
                    Paragraph(Text(
                        "Finally suppose t is a unit, and let s be its bounded inverse. Choose a natural n greater than (k‖s‖)² "
                        + "and apply the preceding estimate to ρ=sPₙ. Since t(sPₙ)=Pₙ, it gives "
                        + "‖Pₙ‖² ≤ k‖sPₙ‖ ≤ k‖s‖‖Pₙ‖. The norm of Pₙ is positive, so ‖Pₙ‖ ≤ k‖s‖. "
                        + "Squaring contradicts ‖Pₙ‖²=2n+1 and the choice of n. Thus t is not a unit. "
                        + "The equivalence between noninvertibility and membership of zero in the spectrum proves the conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klausen-2025-lattice-lindbladian-zero-spectrum"),
                    ResolutionKind.Proved)))));

    private static Formula FiniteRangeFormula() => All("r", Naturals(), Matrices(
        Equal(LocalCall("IsFiniteRange", X("r"), X("h"), X("ℓ")),
            And(All("x", Integers(), All("y", Integers(),
                    Imp(Less(CastInteger(X("r")), new Formula.Absolute(Sub(X("x"), X("y")))),
                        Equal(At(X("h"), X("x"), X("y")), Typed(D(0), Complexes()))))),
                All("k", Integers(), All("x", Integers(), All("y", Integers(),
                    Imp(Less(CastInteger(X("r")), At(Qualified("Max", "max"),
                            new Formula.Absolute(Sub(X("x"), X("k"))),
                            new Formula.Absolute(Sub(X("y"), X("k"))))),
                        Equal(At(X("ℓ"), X("k"), X("x"), X("y")), Typed(D(0), Complexes()))))))))));

    private static Formula TranslationFormula() => Matrices(
        Equal(LocalCall("IsTranslationInvariant", X("h"), X("ℓ")),
            And(All("x", Integers(), All("y", Integers(),
                    Equal(At(X("h"), Add(X("x"), D(1)), Add(X("y"), D(1))),
                        At(X("h"), X("x"), X("y"))))),
                All("k", Integers(), All("x", Integers(), All("y", Integers(),
                    Equal(At(X("ℓ"), Add(X("k"), D(1)), Add(X("x"), D(1)), Add(X("y"), D(1))),
                        At(X("ℓ"), X("k"), X("x"), X("y")))))))));

    private static Formula EntryFormula()
    {
        Formula left = SumOver("z", Mul(At(X("h"), X("x"), X("z")), At(X("ρ"), Pair(X("z"), X("y")))));
        Formula right = SumOver("z", Mul(At(X("ρ"), Pair(X("x"), X("z"))), At(X("h"), X("z"), X("y"))));
        Formula gain = SumOver("u", SumOver("v", Mul(
            Mul(At(X("ℓ"), X("k"), X("x"), X("u")), At(X("ρ"), Pair(X("u"), X("v")))),
            StarOf(At(X("ℓ"), X("k"), X("y"), X("v"))))));
        Formula leftLoss = SumOver("z", Mul(
            SumOver("w", Mul(StarOf(At(X("ℓ"), X("k"), X("w"), X("x"))), At(X("ℓ"), X("k"), X("w"), X("z")))),
            At(X("ρ"), Pair(X("z"), X("y")))));
        Formula rightLoss = SumOver("z", Mul(At(X("ρ"), Pair(X("x"), X("z"))),
            SumOver("w", Mul(StarOf(At(X("ℓ"), X("k"), X("w"), X("z"))), At(X("ℓ"), X("k"), X("w"), X("y"))))));
        Formula half = new Formula.Fraction(Typed(D(1), Complexes()), Typed(D(2), Complexes()));
        Formula body = Add(Mul(new Formula.Negate(Qualified("Complex", "I")), Sub(left, right)),
            Mul(At(Qualified("Complex", "ofReal"), X("g")),
                SumOver("k", Sub(Sub(gain, Mul(half, leftLoss)), Mul(half, rightLoss)))));
        return All("g", Reals(), Matrices(All("ρ", Arrow(Pairs(), Complexes()),
            All("x", Integers(), All("y", Integers(),
                Equal(Typed(LocalCall("lindbladEntry", X("g"), X("h"), X("ℓ"), X("ρ"), X("x"), X("y")), Complexes()), body))))));
    }

    private static Formula ResultFormula()
    {
        Formula entries = All("ρ", HilbertSpace(), All("x", Integers(), All("y", Integers(),
            Equal(At(KernelFunction(At(At(Qualified("DFunLike", "coe"), X("t")), X("ρ"))), Pair(X("x"), X("y"))),
                LocalCall("lindbladEntry", X("g"), X("h"), X("ℓ"), KernelFunction(X("ρ")), X("x"), X("y"))))));
        Formula spectralZero = new Formula.Relation(Typed(D(0), Complexes()), FormulaRelationOperator.MemberOf,
            At(Qualified("spectrum"), Complexes(), X("t")));
        return All("r", Naturals(), All("g", Reals(), Matrices(
            Imp(LocalCall("IsFiniteRange", X("r"), X("h"), X("ℓ")),
                Imp(LocalCall("IsTranslationInvariant", X("h"), X("ℓ")),
                    Some("t", Endomorphisms(), And(entries, spectralZero)))))));
    }

    private static Formula X(string name) => name switch
    {
        "ℓ" => Ell,
        "ρ" => Rho,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Qualified("D5", "S3", "QuantumChannels", "LatticeLindbladianZeroSpectrum", name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Pairs() => Parenthesized(Seq(Integers(), Sp, Times, Sp, Integers()));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula MatrixType() => Arrow(Integers(), Arrow(Integers(), Complexes()));
    private static Formula JumpType() => Arrow(Integers(), MatrixType());
    private static Formula HilbertSpace() => At(Qualified("CoeSort", "coe"),
        At(Qualified("D5", "S3", "Observer", "Approximation",
            "ReadoutUpdateCommutatorFactorization", "ObserverHilbertSpace"), Pairs()));
    private static Formula Endomorphisms() => Seq(HilbertSpace(), Sp,
        new Formula.Subscript(To, F.Id("L")), OpenBracket, Complexes(), CloseBracket, Sp, HilbertSpace());
    private static Formula CastInteger(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Integers());
    private static Formula KernelFunction(Formula value) => At(Qualified("Subtype", "val"), value);
    private static Formula StarOf(Formula value) => At(Qualified("Star", "star"), value);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Matrices(Formula body) => All("h", MatrixType(), All("ℓ", JumpType(), body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Seq(Sum, Apos), Seq(X(name), Colon, Sp, Integers())), Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
