using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class StabilizerAsymmetryShannonBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/tarabunga2025asymmetry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-qubit state violates the proposed Shannon entropy lower bound for stabilizer bases.",
        H("A counterexample to the Shannon branch-and-bound lower bound"),
        Blocks(
            Definition("strict-upper", "IsStrictUpper", "The strictly upper-triangular part", StrictUpperFormula(),
                "A matrix is strictly upper triangular when every entry on or below its diagonal is zero. "
                    + "This is the condition on the off-diagonal part Q′ in the splitting Q = Qd + Q′ of draft.tex line 769."),
            Definition("stab-amp", "stabAmp", "Stabilizer amplitudes", StabAmpFormula(),
                "The amplitude is the stabilizer standard form of draft.tex lines 757–764 with k = N and R equal to the identity, "
                    + "so the translation quotient has one element. Its magnitude factor is the inverse square root of two to the power n. "
                    + "Mathlib's Matrix.toQuadraticForm' computes the quadratic exponent xᵀqx in ZMod 2, "
                    + "which is then represented by its natural value zero or one. "
                    + "The exponent of Complex.I is instead the natural-number sum of the products of the natural representatives of c i and x i; "
                    + "this sum is not reduced modulo two. The definition allows arbitrary q; a stabilizer basis uses Matrix.diagonal d + q "
                    + "with q strictly upper triangular. Mathlib's Matrix.diagonal has entries d i on the diagonal and zero elsewhere."),
            Definition("overlap-prob", "overlapProb", "Squared stabilizer overlaps", OverlapProbFormula(),
                "For a fixed q, c and state ψ, the value at d is the squared complex norm of the overlap with "
                    + "the stabilizer amplitude whose matrix is Matrix.diagonal d + q. Complex conjugation acts on the stabilizer amplitude. "
                    + "This specializes the distribution p of draft.tex line 769 to k = N and R equal to the identity. "
                    + "The function is defined for arbitrary ψ, q and c; the unit-vector and triangular conditions enter the conjecture."),
            Definition("abs-prob", "absProb", "Squared overlaps after taking absolute amplitudes", AbsProbFormula(),
                "Replace each state amplitude by its nonnegative real norm, included in the complex scalars, "
                    + "and use Matrix.diagonal d with zero c. The resulting squared overlaps specialize the distribution qR "
                    + "of draft.tex line 776 to R equal to the identity. Function.const denotes the zero binary vector in the displayed formula."),
            Describe.Lean(
                DescribeId.Create("shannon-bound-sum-bits"), DeclarationHandle.Create(Prefix + "sum_bits"),
                H("A sum over the eight binary words"), StatementSource.FromAuthor(Disp(SumBitsFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any type A in any universe with an additive commutative monoid structure, "
                        + "the sum of f over all functions Fin 3 to ZMod 2 is the displayed eight-term sum. "
                        + "The coordinates are ordered 0, 1, 2, with zero before one in each coordinate."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("shannon-bound-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The Shannon lower-bound assertion"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive number of qubits and every unit complex amplitude vector, the Shannon entropy of the absolute-amplitude law "
                        + "is asserted to be no greater than the entropy for each strictly upper-triangular q and each binary c. "
                        + "Shannon entropy is the finite sum of −r log r in nats, with the summand zero at r = 0. "
                        + "This is the k = N, R = I specialization of the conjectured Shannon extension of equation (69): "
                        + "draft.tex lines 776–779 give the bound for integer Rényi index greater than one, and line 782 conjectures it for index one. "
                        + "A lower bound on the minimum over q and c requires the same lower bound for every such pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shannon-bound-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The three-qubit entropy reversal"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = 3 and the real vector v = (1,0,2,−1,1,0,0,1), in binary order 000,001,010,011,100,101,110,111, "
                            + "with coordinate zero most significant. Include v in the complex scalars and put ψ = v/√8. "
                            + "Enumerating the eight binary strings gives the squared norm "
                            + "(1 + 0 + 4 + 1 + 1 + 0 + 0 + 1)/8 = 1.")),
                    Paragraph(Text(
                        "FourMUBBoundEntanglementRefutation.scale_sq gives (√8)⁻² = 1/8. "
                            + "Consequently, for each pair d,x of three-bit strings, "
                            + "the overlap summand at q = 0 and c = 0 is (−1) to the natural representative of "
                            + "Matrix.toQuadraticForm' (Matrix.diagonal d) x, "
                            + "times v x divided by eight, all in the complex scalars. The corresponding absolute-amplitude summand "
                            + "has |v x| in place of v x. The quadratic exponent is computed in ZMod 2 before taking its natural representative.")),
                    Paragraph(Text(
                        "Splitting each coordinate of d into its two possible values and summing over the eight x gives "
                            + "overlapProb 0 0 ψ = (1/4,1/4,0,0,0,1/4,0,1/4), "
                            + "whereas absProb ψ = (9/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16), in the same binary order.")),
                    Paragraph(Text(
                        "Apply OrientationEntropyBalance.sum_entropy_formula first to four counts all equal to one with total four, "
                            + "and then to the eight counts (9,1,1,1,1,1,1,1) with total sixteen. "
                            + "Expanding Real.logb and clearing the positive factor log 2 converts the formula to natural logarithms. "
                            + "The power identities log 4 = 2 log 2, log 16 = 4 log 2 and log (9⁹) = 18 log 3, "
                            + "together with the displayed distributions and the zero Shannon summands, "
                            + "give respectively 2 log 2 and 4 log 2 − (9/8) log 3.")),
                    Paragraph(Text(
                        "The upper bound in TwoDeletionRunEntropyBounds.logb_three_bounds is logb 2 3 < 5/3. "
                            + "Expand Real.logb and use log 2 > 0 to obtain 9 log 3 < 15 log 2 < 16 log 2. "
                            + "Now apply the asserted inequality to n = 3, the unit vector ψ and the zero q and c; "
                            + "the zero matrix is strictly upper triangular because every entry is zero. "
                            + "The two entropy values would give 4 log 2 − (9/8) log 3 ≤ 2 log 2, "
                            + "contradicting the strict logarithmic inequality. Thus the Shannon lower bound fails already for k = N = 3 and R = I."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tarabunga-frau-haug-tirrito-piroli-2025-shannon-branch-bound"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("shannon-bound-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula StrictUpperFormula() => All("n", Naturals(), All("q", MatrixType(),
        Equivalence(LocalCall("IsStrictUpper", X("q")), All("i", FinOf(X("n")), All("j", FinOf(X("n")),
            Arrow(new Formula.Not(Parenthesized(LessThan(X("i"), X("j")))),
                Equal(At(X("q"), X("i"), X("j")), Typed(D(0), BinaryField()))))))));

    private static Formula StabAmpFormula()
    {
        Formula root = At(Qualified("Real", "sqrt"), new Formula.Power(Typed(D(2), Reals()), X("n")));
        Formula scale = At(Qualified("Inv", "inv"), Typed(At(Qualified("Complex", "ofReal"), root), Complexes()));
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(Typed(D(1), Complexes()))),
            At(Qualified("ZMod", "val"), At(Seq(Operatorname,
                Grp(F.Id("Matrix"), Dot, F.Id("toQuadraticForm"), Apos)), X("q"), X("x"))));
        Formula phase = new Formula.Power(Qualified("Complex", "I"), SumOver("i", FinOf(X("n")),
            Multiply(At(Qualified("ZMod", "val"), At(X("c"), X("i"))),
                At(Qualified("ZMod", "val"), At(X("x"), X("i"))))));
        return All("n", Naturals(), All("q", MatrixType(), All("c", BinaryType(X("n")), All("x", BinaryType(X("n")),
            Equal(LocalCall("stabAmp", X("q"), X("c"), X("x")), Multiply(Multiply(scale, sign), phase))))));
    }

    private static Formula OverlapProbFormula() => All("n", Naturals(), All("q", MatrixType(), All("c", BinaryType(X("n")),
        All("ψ", StateType(), All("d", BinaryType(X("n")), Equal(LocalCall("overlapProb", X("q"), X("c"), X("ψ"), X("d")),
            At(Qualified("Complex", "normSq"), SumOver("x", BinaryType(X("n")),
                Multiply(At(Qualified("Star", "star"), LocalCall("stabAmp",
                    Parenthesized(Add(At(Qualified("Matrix", "diagonal"), X("d")), X("q"))), X("c"), X("x"))),
                    At(X("ψ"), X("x")))))))))));

    private static Formula AbsProbFormula() => All("n", Naturals(), All("ψ", StateType(), All("d", BinaryType(X("n")),
        Equal(LocalCall("absProb", X("ψ"), X("d")), At(Qualified("Complex", "normSq"), SumOver("x", BinaryType(X("n")),
            Multiply(At(Qualified("Star", "star"), LocalCall("stabAmp", At(Qualified("Matrix", "diagonal"), X("d")),
                At(Qualified("Function", "const"), FinOf(X("n")), Typed(D(0), BinaryField())), X("x"))),
                At(Qualified("Complex", "ofReal"), new Formula.Norm(At(X("ψ"), X("x")))))))))));

    private static Formula ClaimFormula()
    {
        Formula unit = Equal(SumOver("x", BinaryType(X("n")), At(Qualified("Complex", "normSq"), At(X("ψ"), X("x")))),
            Typed(D(1), Reals()));
        Formula inequality = LE(Entropy(LocalCall("absProb", X("ψ"))), Entropy(LocalCall("overlapProb", X("q"), X("c"), X("ψ"))));
        return Equivalence(Local("claim"), All("n", Naturals(), Arrow(LE(D(1), X("n")), All("ψ", StateType(),
            Arrow(unit, All("q", MatrixType(), All("c", BinaryType(X("n")), Arrow(LocalCall("IsStrictUpper", X("q")), inequality))))))));
    }

    private static Formula SumBitsFormula()
    {
        Formula words = BinaryType(D(3));
        Formula Term(byte a, byte b, byte c) => At(X("f"),
            Seq(Bang, OpenBracket, D(a), Comma, Sp, D(b), Comma, Sp, D(c), CloseBracket));
        Formula right = Add(Add(Add(Add(Add(Add(Add(
            Term(0, 0, 0), Term(0, 0, 1)), Term(0, 1, 0)), Term(0, 1, 1)),
            Term(1, 0, 0)), Term(1, 0, 1)), Term(1, 1, 0)), Term(1, 1, 1));
        return All("A", Seq(Qualified("Type"), Star),
            Seq(OpenBracket, At(Qualified("AddCommMonoid"), X("A")), CloseBracket, Sp,
                All("f", Arrow(words, X("A")),
                    Equal(SumOver("x", words, At(X("f"), X("x"))), right))));
    }

    private static Formula X(string name) => name == "ψ" ? Psi : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Magic", "StabilizerAsymmetryShannonBoundRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula BinaryField() => At(Qualified("ZMod"), D(2));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula BinaryType(Formula n) => Arrow(FinOf(n), BinaryField());
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("n")), FinOf(X("n")), BinaryField());
    private static Formula StateType() => Arrow(BinaryType(X("n")), Complexes());
    private static Formula Entropy(Formula p) => At(Qualified("D5", "S3", "Entropy", "MaxEntropy", "shannonEntropy"), p);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LessThan(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
