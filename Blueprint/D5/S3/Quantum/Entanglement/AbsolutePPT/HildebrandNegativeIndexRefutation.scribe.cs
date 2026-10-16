using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class HildebrandNegativeIndexRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/chenklco2026negativityrank");
    private static readonly LibraryNoteRef Hildebrand =
        LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible Hildebrand matrix for a four-by-four bipartite spectrum has at least two negative eigenvalues.",
        H("Two negative eigenvalues in a Hildebrand matrix"), Blocks(
            Paragraph(Text(
                "Fin(d) consists of the indices 0 through d − 1. Increments denotes "
                    + "D5.S3.Arith.Lattices.Klartag.Walk.Increments. Its type Increments.UT(d) "
                    + "is the upper triangle {(i,j) : Fin(d) × Fin(d) | i ≤ j}. "
                    + "NikolovSegal.SLnRootAction.PositiveIndex(d) is the strict upper triangle "
                    + "{(i,j) : Fin(d) × Fin(d) | i < j}. Subtype.val forgets the inequality, "
                    + "and Subtype.property supplies it; Prod.fst and Prod.snd select the coordinates. "
                    + "Equiv(S,T) is the type of bijections from S to T. Fintype.card is finite cardinality. "
                    + "Fin.castLE(r) denotes the value-preserving inclusion into the displayed target Fin type, "
                    + "with its inequality proof suppressed. Fin.rev reverses the target order. "
                    + "Matrix.conjTranspose is conjugate transpose. RHLinalg.negIndex takes Hermitian evidence "
                    + "and counts the strictly negative eigenvalues with multiplicity.")),
            Node("PlusOrdering", "Ordering the upper triangle", OrderingFormula(true),
                "An ordering assigns each pair i ≤ j a distinct zero-based rank. "
                    + "There are d(d + 1)/2 pairs, including the diagonal. Adding one to every rank "
                    + "gives Hildebrand's ordering of S₊ onto {1,…,d(d + 1)/2}.",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("MinusOrdering", "Ordering the strict upper triangle", OrderingFormula(false),
                "An ordering assigns each pair i < j a distinct zero-based rank. "
                    + "There are d(d − 1)/2 pairs. Adding one to each rank gives Hildebrand's ordering of S₋.",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("minusToPlus", "Including the strict upper triangle", InclusionFormula(),
                "The inclusion retains the coordinate pair and uses i < j to obtain i ≤ j. "
                    + "It lets the plus ordering act on the pairs of S₋.",
                AssessedProvenance.FromRepo(Hildebrand)),
            Node("Compatible", "Compatibility of the two orderings", CompatibilityFormula(),
                "Hildebrand's Definition 1 requires the products xᵢxⱼ to decrease weakly as the plus rank increases. "
                    + "On the strict upper triangle, the minus ordering must respect the plus ordering. "
                    + "Ties among products are allowed. This predicate is defined for every real vector x; "
                    + "strict decrease and positivity of x enter the next definition.",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("Admissible", "The set of admissible pairs Σ±", AdmissibilityFormula(),
                "A pair belongs to Hildebrand's Σ± exactly when it is compatible with some strictly decreasing "
                    + "positive vector. StrictAnti(x) means xⱼ < xᵢ whenever i < j. "
                    + "The existential condition includes every compatible ordering arising from such a vector.",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("plusIndex", "Reversing a plus rank in the spectrum", IndexFormula(true),
                "The plus rank r is included in Fin(d²) and then reversed, so its spectrum index has value d² − 1 − r. "
                    + "If the one-based rank is σ₊ = r + 1, this is the source entry λ_{d²+1−σ₊}. "
                    + "The inclusion exists because the upper triangle is a subset of Fin(d) × Fin(d).",
                AssessedProvenance.FromRepo(Hildebrand)),
            Node("minusIndex", "Including a minus rank in the spectrum", IndexFormula(false),
                "The minus rank keeps its value when included in Fin(d²). "
                    + "For the one-based rank σ₋ = r + 1, the corresponding source entry is λ_{σ₋}. "
                    + "The strict upper triangle is a subset of Fin(d) × Fin(d), giving the required cardinality bound.",
                AssessedProvenance.FromRepo(Hildebrand)),
            Node("hildebrandArray", "The signed spectral array Λ", ArrayFormula(),
                "The upper triangle, including the diagonal, contains the smallest eigenvalues in the reversed plus order. "
                    + "The lower triangle contains the negatives of the largest eigenvalues in the minus order, "
                    + "with the pair transposed to lie in S₋. All entries are real numbers viewed in the complex field. "
                    + "This is Hildebrand's array Λ in equation (2).",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("hildebrandMatrix", "The Hermitian matrix Λ + Λᴴ", MatrixFormula(),
                "Adding the conjugate transpose gives the matrix of the spectral inequality. "
                    + "Because Λ has real entries, Λᴴ equals Λᵀ, so this is the real symmetric matrix Λ + Λᵀ "
                    + "from Hildebrand's criterion.",
                AssessedProvenance.FromLiterature(Hildebrand)),
            Node("hildebrandMatrix_isHermitian", "Hermitian symmetry", HermitianFormula(),
                "The conjugate transpose of A + Aᴴ is A + Aᴴ. Thus the spectral matrix is Hermitian "
                    + "for every real list and every pair of orderings. Its eigenvalues are real, "
                    + "so its negative index is defined.",
                AssessedProvenance.FromRepo(Hildebrand), DescribeRole.Theorem),
            Node("OrderedSpectrum", "An ordered normalized spectrum", SpectrumFormula(),
                "The d² real entries decrease weakly, are nonnegative, and sum to one. "
                    + "These are precisely the conditions on an ordered list of eigenvalues of a density matrix.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "The proposed persistence of negative index at most one", ClaimFormula(),
                "Theorem II.1 of Chen and Klco identifies the two qutrit matrices in equation (5), "
                    + "and Theorem II.2 bounds each negative index by one for every ordered qutrit spectrum. "
                    + "Section V asks whether this bound persists for the corresponding inequalities when d > 3. "
                    + "The statement here expresses that proposed extension for every dimension d > 3, "
                    + "every ordered normalized spectrum, and every pair in Hildebrand's Σ±. "
                    + "The count includes multiplicity. A real orthogonal diagonalization is also a complex unitary "
                    + "diagonalization of this same real matrix, so using complex entries preserves the eigenvalue list.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("hildebrand-negative-index-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 4 and λ = (13,13,13,13,1,1,1,1,1,1,1,1,1,1,1,1)/64. "
                            + "The entries are nonnegative and decreasing, and their sum is (4·13 + 12)/64 = 1. "
                            + "For x = (8,5,3,1), the upper-triangle pairs in increasing plus rank are "
                            + "(0,0), (0,1), (1,1), (0,2), (1,2), (2,2), (0,3), (1,3), (2,3), (3,3). "
                            + "Their products are 64,40,25,24,15,9,8,5,3,1. The strict upper-triangle pairs "
                            + "in increasing minus rank are (0,1), (0,2), (1,2), (0,3), (1,3), (2,3). "
                            + "Both rank lists start at zero. The vector is strictly decreasing and positive, "
                            + "so these compatible orderings belong to Σ±.")),
                    Paragraph(Text(
                        "For these data, write L for the Hildebrand matrix. Then L = M/32, where "
                            + "M = [[1,−6,−6,−6], [−6,1,−6,0], [−6,−6,1,0], [−6,0,0,1]]. "
                            + "Let B = [[1,0], [0,1], [0,1], [1,−2]]. Direct multiplication gives "
                            + "BᴴLB = −(1/16)[[5,1], [1,3]]. The matrix (1/16)[[5,1], [1,3]] "
                            + "is positive definite: it equals diag(1/4,1/8) + VᴴV, where V = [[1/4,1/4]]. "
                            + "Its negative therefore has two strictly negative eigenvalues. "
                            + "A compression BᴴLB cannot have more negative eigenvalues than L, "
                            + "so L has at least two. This contradicts the asserted bound of one."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chen-klco-2026-hildebrand-negative-index-persistence"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(
            DescribeId.Create("hildebrand-negative-index-" + declaration.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            var words = part.Split('_');
            Formula suffix = N(words[^1]);
            for (var i = words.Length - 2; i >= 0; --i)
                suffix = Seq(N(words[i]), Underscore, Grp(suffix));
            items.Add(Operatorname);
            items.Add(Grp(suffix));
        }
        return Seq([.. items]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(N(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Square() => Mul(N("d"), N("d"));
    private static Formula PlusSet() => Call("Increments.UT", N("d"));
    private static Formula MinusSet() => Call("NikolovSegal.SLnRootAction.PositiveIndex", N("d"));
    private static Formula Card(Formula type) => Call("Fintype.card", type);
    private static Formula SpectrumType() => new Formula.TypeArrow(FinOf(Square()), N("Real"));
    private static Formula MatrixType() => Call("Matrix", FinOf(N("d")), FinOf(N("d")), N("Complex"));
    private static Formula OrderType(bool plus) => Call(plus ? "PlusOrdering" : "MinusOrdering", N("d"));
    private static Formula OrderBinders(Formula body) =>
        All("sigmaP", OrderType(true), All("sigmaM", OrderType(false), body));
    private static Formula MatrixBinders(Formula body) =>
        All("d", N("Nat"), All("lam", SpectrumType(), OrderBinders(body)));
    private static Formula WithMatrixArguments(string name) =>
        Call(name, N("d"), N("lam"), N("sigmaP"), N("sigmaM"));
    private static Formula CompatibleCall() => Call("Compatible", N("sigmaP"), N("sigmaM"), N("x"));
    private static Formula AdmissibleCall() => Call("Admissible", N("sigmaP"), N("sigmaM"));
    private static Formula Coordinate(Formula pair, bool first) =>
        Call(first ? "Prod.fst" : "Prod.snd", Call("Subtype.val", pair));
    private static Formula Product(Formula pair) =>
        Mul(At(N("x"), Coordinate(pair, true)), At(N("x"), Coordinate(pair, false)));

    private static Formula OrderingFormula(bool plus)
    {
        var type = plus ? PlusSet() : MinusSet();
        return All("d", N("Nat"), Eq(OrderType(plus), Call("Equiv", type, FinOf(Card(type)))));
    }

    private static Formula InclusionFormula() => All("d", N("Nat"), All("p", MinusSet(),
        Eq(Typed(Call("minusToPlus", N("p")), PlusSet()),
            Call("Subtype.mk", Call("Subtype.val", N("p")),
                Call("le_of_lt", Call("Subtype.property", N("p")))))));

    private static Formula CompatibilityFormula()
    {
        var plusOrder = All("p", PlusSet(), All("q", PlusSet(),
            Imp(Lt(At(N("sigmaP"), N("p")), At(N("sigmaP"), N("q"))),
                Le(Product(N("q")), Product(N("p"))))));
        var minusOrder = All("p", MinusSet(), All("q", MinusSet(),
            Imp(Lt(At(N("sigmaP"), Call("minusToPlus", N("p"))),
                    At(N("sigmaP"), Call("minusToPlus", N("q")))),
                Lt(At(N("sigmaM"), N("p")), At(N("sigmaM"), N("q"))))));
        return All("d", N("Nat"), OrderBinders(All("x", new Formula.TypeArrow(FinOf(N("d")), N("Real")),
            IffFormula(CompatibleCall(), And(plusOrder, minusOrder)))));
    }

    private static Formula AdmissibilityFormula()
    {
        var positive = All("i", FinOf(N("d")), Lt(D(0), At(N("x"), N("i"))));
        var conditions = And(Call("StrictAnti", N("x")), And(positive, CompatibleCall()));
        return All("d", N("Nat"), OrderBinders(IffFormula(AdmissibleCall(),
            Some("x", new Formula.TypeArrow(FinOf(N("d")), N("Real")), conditions))));
    }

    private static Formula IndexFormula(bool plus)
    {
        var rankType = FinOf(Card(plus ? PlusSet() : MinusSet()));
        var embedded = Typed(Call("Fin.castLE", N("r")), FinOf(Square()));
        return All("d", N("Nat"), All("r", rankType,
            Eq(Typed(Call(plus ? "plusIndex" : "minusIndex", N("r")), FinOf(Square())),
                plus ? Call("Fin.rev", embedded) : embedded)));
    }

    private static Formula ArrayFormula()
    {
        var upperPair = Call("Subtype.mk", Pair(N("i"), N("j")), N("hij"));
        var lowerPair = Call("Subtype.mk", Pair(N("j"), N("i")), Call("lt_of_not_ge", N("hij")));
        var upper = Typed(At(N("lam"), Call("plusIndex", At(N("sigmaP"), upperPair))), N("Complex"));
        var lower = new Formula.Negate(
            Typed(At(N("lam"), Call("minusIndex", At(N("sigmaM"), lowerPair))), N("Complex")));
        var entry = Seq(Q("if"), Sp, Typed(N("hij"), Le(N("i"), N("j"))), Sp,
            Q("then"), Sp, upper, Sp, Q("else"), Sp, lower);
        return MatrixBinders(Eq(Typed(WithMatrixArguments("hildebrandArray"), MatrixType()),
            Lambda("i", FinOf(N("d")), Lambda("j", FinOf(N("d")), entry))));
    }

    private static Formula MatrixFormula() => MatrixBinders(
        Eq(Typed(WithMatrixArguments("hildebrandMatrix"), MatrixType()),
            Add(WithMatrixArguments("hildebrandArray"),
                Call("Matrix.conjTranspose", WithMatrixArguments("hildebrandArray")))));

    private static Formula HermitianFormula() => MatrixBinders(
        Call("Matrix.IsHermitian", WithMatrixArguments("hildebrandMatrix")));

    private static Formula SpectrumFormula()
    {
        var sum = Seq(new Formula.Subscript(Sum, Seq(N("i"), Colon, FinOf(Square()))),
            Parenthesized(At(N("lam"), N("i"))));
        return All("d", N("Nat"), All("lam", SpectrumType(),
            IffFormula(Call("OrderedSpectrum", N("d"), N("lam")),
                And(Call("Antitone", N("lam")), And(
                    All("i", FinOf(Square()), Le(D(0), At(N("lam"), N("i")))), Eq(sum, D(1)))))));
    }

    private static Formula ClaimFormula() => IffFormula(N("claim"),
        All("d", N("Nat"), Imp(Lt(D(3), N("d")), All("lam", SpectrumType(),
            Imp(Call("OrderedSpectrum", N("d"), N("lam")), OrderBinders(
                Imp(AdmissibleCall(), Le(
                    Call("RHLinalg.negIndex", WithMatrixArguments("hildebrandMatrix_isHermitian")), D(1)))))))));
}
