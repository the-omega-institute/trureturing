using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AsynchronousIterationSpectralRadiusRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/aksoyetal2023asynchrony");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real matrix of spectral radius one half has a unit-delay asynchronous iteration of spectral radius at least five quarters.",
        H("Stable synchronous iteration can become unstable with unit remote delays"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("async-matrix"),
                DeclarationHandle.Create(Prefix + "asyncMatrix"),
                H("The matrix acting on the stacked history"),
                StatementSource.FromAuthor(Disp(AsyncMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The block index type Vtx n is the dependent sum of Fin (n i) over i in Fin ℓ. "
                    + "A history coordinate is a pair consisting of a slot and a block coordinate; slot zero is the newest iterate. "
                    + "At slot zero, the entry M p q is taken from the slot whose natural index is δ j i, "
                    + "where i is the block of p and j is the block of q. Every later slot copies the preceding slot at the same coordinate. "
                    + "Fin.val explicitly converts a slot to its natural index. This is the operator M^(δ,k) of "
                    + "Sections/ratfish.tex, lines 48–49, when k bounds all delays. "
                    + "The definition itself accepts every natural k and every delay array; a delay greater than k contributes no entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radius"),
                DeclarationHandle.Create(Prefix + "radius"),
                H("The complex spectral radius of a real matrix"),
                StatementSource.FromAuthor(Disp(RadiusFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Map every real matrix entry into the complex numbers and take the complex spectral radius, "
                    + "with values in the extended nonnegative reals. The map is the function underlying algebraMap ℝ ℂ. "
                    + "This expresses the spectral radius used for real iteration matrices in Sections/ratfish.tex, lines 48–49."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("The block sizes, delays and original radius"),
                StatementSource.FromAuthor(Disp(AdmissibleFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Each block is nonempty, each local delay is zero, and each remote delay lies between one and k, inclusive. "
                    + "The real number lambda lies strictly between zero and one and equals the original spectral radius "
                    + "after inclusion into the extended nonnegative reals. These conditions select positive remote delays "
                    + "from the patterns considered in Sections/ratfish.tex, line 76. "
                    + "The displayed implications impose bounds only on distinct block indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q-one"),
                DeclarationHandle.Create(Prefix + "Q1"),
                H("The proposed power bound"),
                StatementSource.FromAuthor(Disp(QOneFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every choice of block sizes, matrix and admissible delays, the delayed radius would be "
                    + "at most lambda to the real power 1/(k+1). The natural delay bound k is explicitly cast to a real "
                    + "number before adding the real one in the denominator. "
                    + "This is the first question of Sections/ratfish.tex, lines 75–77, restricted to the stated admissible data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q-two"),
                DeclarationHandle.Create(Prefix + "Q2"),
                H("A uniform bound below one"),
                StatementSource.FromAuthor(Disp(QTwoFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "One real-valued function f of lambda and the natural delay bound k would bound every admissible delayed radius. "
                    + "For every k and every lambda strictly between zero and one, its value must also lie strictly between zero and one. "
                    + "The function is defined on all real lambda, with no range condition outside this interval. "
                    + "On the interval this states the second question of Sections/ratfish.tex, lines 75–77, for the admissible data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("At least one proposed bound holds"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"),
                    Disjunction(Local("Q1"), Local("Q2"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The assertion is the disjunction of the power bound and the existence of a uniform bound below one. "
                    + "Both alternatives quantify over arbitrary block arrays and the same admissible delay patterns. "
                    + "Positive remote delays and positive lambda suffice to test both questions in Sections/ratfish.tex, lines 75–77."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both bounds fail for two scalar blocks"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take two blocks of size one and the real matrix M with rows (7/4, 5/4) and (−5/4, −3/4). "
                        + "Let A be its entrywise complexification. Direct multiplication gives (A − (1/2)I)² = 0. "
                        + "If z belongs to the complex spectrum of A, spectral translation places z − 1/2 in the spectrum "
                        + "of A − (1/2)I. Squaring then places (z − 1/2)² in the spectrum of the zero matrix, which is {0}, "
                        + "so z = 1/2. Conversely, (1/2)I − A is nilpotent, hence is not a unit, so 1/2 belongs to the spectrum of A. "
                        + "The spectrum is therefore exactly {1/2}, and the supremum of the nonnegative complex norms gives radius M = 1/2.")),
                    Paragraph(Text(
                        "Set k = 1 and take the delay array with rows (0,1) and (1,0), the natural adjacency matrix "
                        + "of the complete simple graph on Fin 2. Both block sizes are positive, the diagonal delays vanish, "
                        + "the remote delays equal one, and lambda = 1/2 lies in (0,1). Together with the radius calculation, "
                        + "these facts give all the admissibility conditions.")),
                    Paragraph(Text(
                        "In the order consisting of the two newest coordinates followed by the two preceding coordinates, "
                        + "the asynchronous matrix B has rows (7/4,0,0,5/4), (0,−3/4,−5/4,0), (1,0,0,0) and (0,1,0,0). "
                        + "The complex vector v = (10,−5,8,−4) is nonzero because its first coordinate is 10. "
                        + "Multiplying by the complexification of B gives (25/2,−25/4,10,−5) = (5/4)v. "
                        + "Thus 5/4 lies in its complex spectrum. Its nonnegative norm, included into the extended nonnegative reals, "
                        + "is ENNReal.ofReal (5/4); the supremum defining the radius is at least this value.")),
                    Paragraph(Text(
                        "If Q1 held, applying it to these admissible data would bound the delayed radius by "
                        + "ENNReal.ofReal ((1/2)^(1/(1+1))). The real power is at most one because its base lies in [0,1] "
                        + "and its exponent is nonnegative. Monotonicity of ENNReal.ofReal would then give "
                        + "ENNReal.ofReal (5/4) ≤ ENNReal.ofReal 1, a contradiction.")),
                    Paragraph(Text(
                        "If Q2 held, its range condition would give 0 < f (1/2) 1 < 1. Applying its uniform bound "
                        + "to the same data and combining it with the delayed radius lower bound gives "
                        + "ENNReal.ofReal (5/4) ≤ ENNReal.ofReal (f (1/2) 1). Since f (1/2) 1 is nonnegative, "
                        + "this implies 5/4 ≤ f (1/2) 1, contradicting f (1/2) 1 < 1. "
                        + "Each alternative is false, so their disjunction is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AsyncMatrixFormula()
    {
        Formula rp = X("rp"), sq = X("sq");
        Formula r = At(Qualified("Fin", "val"), First(rp));
        Formula s = At(Qualified("Fin", "val"), First(sq));
        Formula delay = At(X("δ"), At(Qualified("Sigma", "fst"), Second(sq)),
            At(Qualified("Sigma", "fst"), Second(rp)));
        Formula update = If(Equal(s, delay), At(X("M"), Second(rp), Second(sq)), Typed(D(0), Reals()));
        Formula shift = If(Conjunction(Equal(Add(s, Typed(D(1), Naturals())), r),
            Equal(Second(sq), Second(rp))), Typed(D(1), Reals()), Typed(D(0), Reals()));
        Formula value = LambdaOf("rp", History(), LambdaOf("sq", History(),
            If(Equal(r, Typed(D(0), Naturals())), update, shift)));
        return All("ℓ", Naturals(), All("n", Arrow(FinOf(X("ℓ")), Naturals()),
            All("M", BlockMatrix(), All("δ", Delays(), All("k", Naturals(),
                Equal(Typed(LocalCall("asyncMatrix", X("M"), X("δ"), X("k")),
                    MatrixOf(History(), Reals())), Parenthesized(value)))))));
    }

    private static Formula RadiusFormula()
    {
        Formula scalarMap = At(Qualified("DFunLike", "coe"), At(Qualified("algebraMap"), Reals(), Complexes()));
        Formula complexification = At(Qualified("Matrix", "map"), X("M"), scalarMap);
        Formula body = All("M", MatrixOf(X("ι"), Reals()),
            Equal(Typed(LocalCall("radius", X("M")), Qualified("ENNReal")),
                At(Qualified("spectralRadius"), Complexes(), complexification)));
        return All("ι", Seq(Qualified("Type"), Star), Seq(
            OpenBracket, At(Qualified("Fintype"), X("ι")), CloseBracket, Sp,
            OpenBracket, At(Qualified("DecidableEq"), X("ι")), CloseBracket, Comma, Sp,
            Parenthesized(body)));
    }

    private static Formula AdmissibleFormula()
    {
        Formula blocks = All("i", FinOf(X("ℓ")), Less(Typed(D(0), Naturals()), At(X("n"), X("i"))));
        Formula local = All("i", FinOf(X("ℓ")), Equal(At(X("δ"), X("i"), X("i")), Typed(D(0), Naturals())));
        Formula remote = All("i", FinOf(X("ℓ")), All("j", FinOf(X("ℓ")),
            Arrow(NotEqual(X("i"), X("j")), Conjunction(
                LE(Typed(D(1), Naturals()), At(X("δ"), X("i"), X("j"))),
                LE(At(X("δ"), X("i"), X("j")), X("k"))))));
        return DataBinders(Equal(Admissible(), Conjunction(blocks, Conjunction(local, Conjunction(remote,
            Conjunction(Less(Typed(D(0), Reals()), X("lambda")),
                Conjunction(Less(X("lambda"), Typed(D(1), Reals())),
                    Equal(LocalCall("radius", X("M")), OfReal(X("lambda"))))))))));
    }

    private static Formula QOneFormula()
    {
        Formula realK = Typed(At(Qualified("Nat", "cast"), X("k")), Reals());
        Formula exponent = new Formula.Fraction(Typed(D(1), Reals()), Add(realK, Typed(D(1), Reals())));
        Formula bound = OfReal(new Formula.Power(Parenthesized(X("lambda")), Parenthesized(exponent)));
        return Equal(Local("Q1"), Parenthesized(DataBinders(Arrow(Admissible(), LE(DelayedRadius(), bound)))));
    }

    private static Formula QTwoFormula()
    {
        Formula value = At(X("f"), X("lambda"), X("k"));
        Formula range = All("lambda", Reals(), All("k", Naturals(),
            Arrow(Less(Typed(D(0), Reals()), X("lambda")),
                Arrow(Less(X("lambda"), Typed(D(1), Reals())),
                    Conjunction(Less(Typed(D(0), Reals()), value), Less(value, Typed(D(1), Reals())))))));
        Formula bound = DataBinders(Arrow(Admissible(), LE(DelayedRadius(), OfReal(value))));
        return Equal(Local("Q2"), Parenthesized(Some("f", Arrow(Reals(), Arrow(Naturals(), Reals())), Conjunction(range, bound))));
    }

    private static Formula DataBinders(Formula body) =>
        All("ℓ", Naturals(), All("n", Arrow(FinOf(X("ℓ")), Naturals()), All("k", Naturals(),
            All("M", BlockMatrix(), All("δ", Delays(), All("lambda", Reals(), body))))));
    private static Formula Admissible() => LocalCall("Admissible", X("ℓ"), X("n"), X("k"), X("M"), X("δ"), X("lambda"));
    private static Formula DelayedRadius() => LocalCall("radius", LocalCall("asyncMatrix", X("M"), X("δ"), X("k")));
    private static Formula OfReal(Formula value) => At(Qualified("ENNReal", "ofReal"), value);
    private static Formula Vertices() => At(Qualified("D5", "S3", "Combinatorics", "Graph", "MultipartiteCHS", "Defs", "Vtx"), X("n"));
    private static Formula BlockMatrix() => MatrixOf(Vertices(), Reals());
    private static Formula Delays() => Arrow(FinOf(X("ℓ")), Arrow(FinOf(X("ℓ")), Naturals()));
    private static Formula History() => Seq(FinOf(Add(X("k"), Typed(D(1), Naturals()))), Sp, Times, Sp, Vertices());
    private static Formula MatrixOf(Formula index, Formula scalar) => At(Qualified("Matrix"), index, index, scalar);
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula First(Formula pair) => Seq(Parenthesized(pair), Dot, D(1));
    private static Formula Second(Formula pair) => Seq(Parenthesized(pair), Dot, D(2));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Matrix", "AsynchronousIterationSpectralRadiusRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "ℓ" => Ell,
        "δ" => DeltaLower,
        "ι" => Iota,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(part switch
            {
                "D5" => Seq(F.Id("D"), D(5)),
                "S3" => Seq(F.Id("S"), D(3)),
                "Q1" => Seq(F.Id("Q"), D(1)),
                "Q2" => Seq(F.Id("Q"), D(2)),
                _ => F.Id(part),
            });
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), Parenthesized(condition), yes, no);
}
