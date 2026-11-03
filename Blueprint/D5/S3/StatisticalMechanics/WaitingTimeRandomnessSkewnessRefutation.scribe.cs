using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class WaitingTimeRandomnessSkewnessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/baratoseifert2015skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eight-state enzyme network has waiting-time skewness at most two and randomness greater than one.",
        H("Waiting-time randomness and skewness on two enzyme routes"),
        Blocks(
            Paragraph(Text(
                "Source line numbers refer to skewkurtstatkinarxiv.tex in "
                    + "Barato and Seifert, arXiv:1510.03279v1.")),
            Node("cemetery", "The generator before product release", CemeteryFormula(),
                "The states are Fin m and k i j is the transition rate from i to j. "
                    + "The diagonal is minus the sum of the off-diagonal exit rates. "
                    + "For distinct p and r, the marked off-diagonal entry is set to zero "
                    + "while its contribution to the exit rate remains on the diagonal. "
                    + "This sends probability to an absorbing cemetery state. "
                    + "This gives a first-passage description of the cycle completion at product release "
                    + "in Barato and Seifert, TeX lines 110–117 and 133–136. "
                    + "The formula also defines a matrix for arbitrary k, p and r, including p = r.",
                AssessedProvenance.FromRepo(Source)),
            Node("moment", "The first-passage moment vectors", MomentFormula(),
                "The zeroth moment is the constant vector one. Each next moment is obtained "
                    + "by multiplying the preceding vector by the inverse of the negative cemetery "
                    + "generator and by the next natural number, cast to a real scalar. "
                    + "When that matrix is invertible, this is the linear system saying that "
                    + "the negative generator applied to the next moment equals the preceding "
                    + "moment multiplied by its order. In the first-passage reading, the "
                    + "component at r is the moment of the completion time starting just "
                    + "after release. This is the first-passage "
                    + "reading of the moments defined in Barato and Seifert, TeX lines 133–136; "
                    + "the definition uses matrix inversion and natural recursion rather than "
                    + "an integral over a stochastic process. It is total even for singular matrices.",
                AssessedProvenance.FromRepo(Source)),
            Node("variance", "The variance at the reset state", VarianceFormula(),
                "At the reset state r, subtract the square of the first moment from the second "
                    + "moment. This expresses the variance in the first-passage moment vectors, "
                    + "corresponding to the squared standard deviation in Barato and Seifert, "
                    + "TeX line 142. Positivity is a separate hypothesis of the proposed inequality.",
                AssessedProvenance.FromRepo(Source)),
            Node("randomness", "The randomness parameter", RandomnessFormula(),
                "Divide the variance by the square of the mean completion time at r. "
                    + "This is the randomness parameter of Barato and Seifert, TeX lines 138–142, "
                    + "expressed in the first-passage moments.",
                AssessedProvenance.FromLiterature(Source)),
            Node("skewness", "The standardized third central moment", SkewnessFormula(),
                "Subtract three times the mean times the variance and the cube of the mean "
                    + "from the third moment, then divide by the cube of the square root of the "
                    + "variance. This is the skewness of Barato and Seifert, TeX lines 142–145. "
                    + "All quantities are evaluated at the reset state r.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsNetwork", "Finite networks with an accessible product transition", NetworkFormula(),
                "Off-diagonal transition rates are nonnegative, the marked rate from p to r "
                    + "is positive, and every state can reach p along a finite path of positive "
                    + "transition rates. Reachability includes the path of length zero. "
                    + "These conditions specify the finite network used for the first-passage "
                    + "reading of cycle completion in Barato and Seifert, TeX lines 110–117 "
                    + "and 133–136. The predicate imposes no diagonal-rate condition or "
                    + "distinctness condition on p and r.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "The proposed implication for arbitrary networks", ClaimFormula(),
                "For every finite network with positive variance, skewness at most two is "
                    + "asserted to imply randomness at most one. Barato and Seifert report "
                    + "this ordering numerically for their two-cycle example in TeX lines "
                    + "341–352 and its off-pathway case in lines 354–357, and ask in line 358 "
                    + "whether it holds for arbitrary networks beyond a single cycle. "
                    + "The displayed proposition gives that implication the finite-network "
                    + "and first-passage meaning defined above.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("waiting-time-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Two routes violate the implication"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the eight states 0 through 7, with marked release from 7 to 0. "
                            + "The nonzero transition rates are 75 from 0 to 1, 25 from 0 to 2, "
                            + "25 from 1 to 7, 5 on each of the transitions from 2 to 3, from 3 to 4, "
                            + "from 4 to 5, from 5 to 6 and from 6 to 7, and 25 from 7 to 0. "
                            + "All other entries are zero. These rates are nonnegative, the marked "
                            + "rate is positive, and each state reaches 7: states 2 through 6 follow "
                            + "the chain, state 1 jumps directly to 7, state 0 goes through 1, "
                            + "and state 7 uses the path of length zero.")),
                    Paragraph(Text(
                        "Negating the cemetery generator gives an upper triangular matrix "
                            + "with diagonal entries 100, 25, 5, 5, 5, 5, 5 and 25. "
                            + "Its off-diagonal entries are the negatives of the listed rates "
                            + "except that the marked entry is zero. Its determinant is the "
                            + "product of the nonzero diagonal entries, so it is invertible. "
                            + "Consequently, a vector mapped by this matrix to n + 1 times the "
                            + "nth moment vector must be the next moment vector.")),
                    Paragraph(Text(
                        "Starting from the constant vector one, three successive matrix-vector "
                            + "identities give the first moment vector "
                            + "(33/100, 2/25, 26/25, 21/25, 16/25, 11/25, 6/25, 1/25), "
                            + "the second moment vector "
                            + "(1673/5000, 6/625, 802/625, 542/625, 332/625, 172/625, 62/625, 2/625), "
                            + "and the third moment vector "
                            + "(234843/500000, 24/15625, 28656/15625, 16626/15625, "
                            + "8496/15625, 3516/15625, 936/15625, 6/15625). "
                            + "Their components at the reset state 0 are respectively "
                            + "33/100, 1673/5000 and 234843/500000.")),
                    Paragraph(Text(
                        "The variance is therefore 2257/10000 and the randomness parameter "
                            + "is 2257/1089, which is greater than one. For the skewness, "
                            + "the square root of 2257/10000 is positive and is at least 19/40, "
                            + "since the square of 19/40 is at most 2257/10000. "
                            + "Cubing preserves this bound. The third central moment is "
                            + "105153/500000, which is at most twice the cube of 19/40, "
                            + "and hence at most twice the cube of the square root of the variance. "
                            + "After multiplying by the positive denominator, this is precisely "
                            + "the inequality that the skewness is at most two.")),
                    Paragraph(Text(
                        "The proposed universal implication, applied to these eight states, "
                            + "the marked transition, the positive variance and the skewness "
                            + "bound, would give randomness at most one. This contradicts "
                            + "the strict lower bound just obtained. The argument concerns "
                            + "the first-passage moment definition above and refutes the "
                            + "randomness-versus-skewness implication asked about in "
                            + "Barato and Seifert, TeX lines 350–358."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barato-seifert-2015-waiting-time-randomness-skewness-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("waiting-time-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CemeteryFormula()
    {
        Formula diagonal = Negate(SumOver("l", FinOf(X("m")),
            IfThenElse(Equal(X("i"), X("l")), Real(D(0)), At(X("k"), X("i"), X("l")))));
        Formula offDiagonal = IfThenElse(
            And(Equal(X("i"), X("p")), Equal(X("j"), X("r"))),
            Real(D(0)), At(X("k"), X("i"), X("j")));
        Formula entries = LambdaOf("i", FinOf(X("m")), LambdaOf("j", FinOf(X("m")),
            IfThenElse(Equal(X("i"), X("j")), diagonal, offDiagonal)));
        return NetworkBinders(Equal(Typed(LocalCall("cemetery"),
            At(Qualified("Matrix"), FinOf(X("m")), FinOf(X("m")), Reals())), entries));
    }

    private static Formula MomentFormula()
    {
        Formula inverse = At(Qualified("Inv", "inv"), Negate(LocalCall("cemetery")));
        Formula scalar = Typed(At(Qualified("Nat", "cast"),
            Typed(Add(X("n"), D(1)), Naturals())), Reals());
        Formula step = LambdaOf("n", Naturals(), LambdaOf("v", VectorType(),
            Smul(scalar, At(Qualified("Matrix", "mulVec"), inverse, X("v")))));
        Formula recursion = At(Qualified("Nat", "rec"),
            At(Qualified("Function", "const"), FinOf(X("m")), Real(D(1))), step, X("t"));
        return NetworkBinders(All("t", Naturals(),
            Equal(Typed(At(LocalCall("moment"), X("t")), VectorType()), recursion)));
    }

    private static Formula VarianceFormula() => NetworkBinders(Equal(
        Typed(LocalCall("variance"), Reals()),
        Subtract(MomentAtReset(2), Power(MomentAtReset(1), 2))));

    private static Formula RandomnessFormula() => NetworkBinders(Equal(
        Typed(LocalCall("randomness"), Reals()),
        new Formula.Fraction(LocalCall("variance"), Power(MomentAtReset(1), 2))));

    private static Formula SkewnessFormula()
    {
        Formula numerator = Subtract(Subtract(MomentAtReset(3),
            Multiply(Multiply(Real(D(3)), MomentAtReset(1)), LocalCall("variance"))),
            Power(MomentAtReset(1), 3));
        Formula denominator = Power(At(Qualified("Real", "sqrt"), LocalCall("variance")), 3);
        return NetworkBinders(Equal(Typed(LocalCall("skewness"), Reals()),
            new Formula.Fraction(numerator, denominator)));
    }

    private static Formula NetworkFormula()
    {
        Formula nonnegative = All("i", FinOf(X("m")), All("j", FinOf(X("m")),
            Arrow(NotEqual(X("i"), X("j")), LE(Real(D(0)), At(X("k"), X("i"), X("j"))))));
        Formula positive = LT(Real(D(0)), At(X("k"), X("p"), X("r")));
        Formula relation = LambdaOf("i", FinOf(X("m")), LambdaOf("j", FinOf(X("m")),
            LT(Real(D(0)), At(X("k"), X("i"), X("j")))));
        Formula reachable = All("i", FinOf(X("m")),
            At(Qualified("Relation", "ReflTransGen"), relation, X("i"), X("p")));
        return NetworkBinders(IffOf(LocalCall("IsNetwork"), And(nonnegative, And(positive, reachable))));
    }

    private static Formula ClaimFormula() => IffOf(Local("claim"), ClaimBody());

    private static Formula ClaimBody() => NetworkBinders(
        Arrow(LocalCall("IsNetwork"),
            Arrow(LT(Real(D(0)), LocalCall("variance")),
                Arrow(LE(LocalCall("skewness"), Real(D(2))),
                    LE(LocalCall("randomness"), Real(D(1)))))));

    private static Formula NetworkBinders(Formula body) => All("m", Naturals(),
        All("k", Arrow(FinOf(X("m")), Arrow(FinOf(X("m")), Reals())),
            All("p", FinOf(X("m")), All("r", FinOf(X("m")), body))));
    private static Formula VectorType() => Arrow(FinOf(X("m")), Reals());
    private static Formula MomentAtReset(byte n) => At(LocalCall("moment"), Typed(D(n), Naturals()), X("r"));
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "WaitingTimeRandomnessSkewnessRefutation", name);
    private static Formula LocalCall(string name) => At(Local(name), X("k"), X("p"), X("r"));
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Real(Formula value) => Typed(value, Reals());
    private static Formula FinOf(Formula value) => At(Qualified("Fin"), value);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula Negate(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Power(Formula value, byte exponent) => new Formula.Power(Parenthesized(value), D(exponent));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
