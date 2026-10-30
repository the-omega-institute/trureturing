using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class MultipartiteEntangledMeasurementPartialTightnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/tavakoliabbottrenougisinbrunner2018sdi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Computational and Fourier bases in disjoint sectors attain every multipartite partial bound with a multiple of d separable outcomes.",
        H("Partial tightness of the multipartite entangled-measurement bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-index"),
                DeclarationHandle.Create(Module + ".jointIndex"),
                H("Joint coordinates"),
                StatementSource.FromAuthor(Disp(JointIndexFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A joint coordinate is a function from the n party indices to the residues modulo d. "
                    + "When n is nonzero, the first party has index zero. This type describes inputs, outcomes and computational basis labels; "
                    + "its definition allows every natural n and d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("winning-outcome"),
                DeclarationHandle.Create(Module + ".winningOutcome"),
                H("The sum-and-difference winning string"),
                StatementSource.FromAuthor(Disp(WinningOutcomeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The coordinate at party zero is the sum of the x inputs; each other coordinate is its y input "
                    + "minus the y input at party zero. All these operations take place in ZMod d. "
                    + "This is the winning condition in SDI_manuscript.tex, lines 150–155, with party indices starting at zero. "
                    + "Only n must be nonzero for this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("score"),
                DeclarationHandle.Create(Module + ".score"),
                H("The average winning probability"),
                StatementSource.FromAuthor(Disp(ScoreFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each pair of input strings, form the tensor product of the chosen local matrices, "
                    + "conjugate ρ by it, and take the real part of the trace against the winning measurement operator. "
                    + "Averaging uniformly over the d to the power 2n input pairs gives the score. "
                    + "The product map is the matrix tensor product on joint coordinates. "
                    + "This specializes the transformations of SDI_manuscript.tex, lines 143–160, to conjugation by local matrices. "
                    + "The definition itself imposes no positivity, normalization or unitarity conditions; those enter the existence statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fully-separable"),
                DeclarationHandle.Create(Module + ".IsFullySeparable"),
                H("Finite sums of positive product operators"),
                StatementSource.FromAuthor(Disp(FullySeparableFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An operator is fully separable when its entries are a finite sum of products of entries of positive "
                    + "semidefinite local matrices. The number k of summands is arbitrary and may be zero. "
                    + "With at least one party, nonnegative scalar weights can be absorbed into the local factors. "
                    + "The definition also allows zero parties, in which case each empty product equals one. "
                    + "This is the fully separable decomposition of SDI_manuscript.tex, line 258."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projective-measurement"),
                DeclarationHandle.Create(Module + ".IsProjectiveMeasurement"),
                H("A complete family of orthogonal projections"),
                StatementSource.FromAuthor(Disp(ProjectiveMeasurementFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every outcome operator is a self-adjoint idempotent, and their sum is the identity matrix. "
                    + "The predicate does not require rank one. It expresses the projective measurements used in "
                    + "SDI_manuscript.tex, lines 193–195 and 478–490."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Multipartite partial tightness"),
                StatementSource.FromAuthor(Disp(IffOf(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every n and d at least two and every natural m at most d^(n − 1), "
                    + "there are a density matrix, local unitary encodings, and a projective measurement with exactly dm "
                    + "fully separable outcome operators and the displayed score. The lower bounds on n and d provide "
                    + "the nonzero instances in the predicates and score. All casts in the score equality are from natural numbers to real numbers. "
                    + "This is the affirmative reading of the question at SDI_manuscript.tex, line 497, extending the "
                    + "bipartite partial tightness at lines 474–496. At k = dm the score equals the right side of "
                    + "Result 2, lines 265–272. The statement concerns the multiples of d and does not assert "
                    + "attainment at other numbers of separable outcomes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Attainment by a choice of basis in each sector"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a joint label r with r(0) = 0, write e(t,r) for the computational vector at the string "
                        + "whose kth coordinate is t + r(k). Every string i has the unique representation "
                        + "t = i(0), r(k) = i(k) − i(0). Thus the sectors indexed by r are disjoint and exhaust the "
                        + "computational basis. Within a sector let g(a,r) have coefficient "
                        + "d⁻¹ᐟ² χ(at) at e(t,r), and zero elsewhere, where χ is the standard additive character of ZMod d. "
                        + "For an outcome b set a = b(0) and r equal to b with its zeroth coordinate replaced by zero. "
                        + "Given a set R of sectors, choose e(a,r) when r belongs to R and g(a,r) otherwise; "
                        + "the outcome operator is the projector onto that vector.")),
                    Paragraph(Text(
                        "Each computational projector is the tensor product of its one-coordinate positive projectors, "
                        + "so it is fully separable. For each party use the clock power Z to the input x times the shift "
                        + "power X to the input y, using the natural representatives of the residues as exponents. "
                        + "The clock and shift matrices are unitary; closure under powers and "
                        + "products makes every local encoding unitary.")),
                    Paragraph(Text(
                        "The Fourier vectors in distinct sectors have disjoint support. Within one sector, their inner "
                        + "product is d⁻¹ times the sum of χ(t(c − a)) over t. Character orthogonality makes this one "
                        + "when a = c and zero otherwise. In particular g(0,0) is normalized, and its outer product "
                        + "is a positive semidefinite density matrix of trace one, the generalized GHZ state. "
                        + "Computational vectors in selected sectors are mutually orthonormal and orthogonal to Fourier "
                        + "vectors in unselected sectors. The selected vectors therefore form an orthonormal family "
                        + "indexed by all joint outcomes. If W has these vectors as columns, W†W = I. "
                        + "Since W is square, WW† = I as well. Each rank-one operator is a self-adjoint idempotent, "
                        + "and their sum is WW†, proving completeness of the measurement.")),
                    Paragraph(Text(
                        "To identify every separable outcome, consider a normalized vector v whose rank-one projector "
                        + "is a sum of positive product matrices Aⱼ. Positivity of these product matrices follows by "
                        + "successive Hadamard products of pulled-back local positive matrices. Reindex the joint basis "
                        + "by Fintype.equivFin and apply summand_kernel from AbsolutelyEntangledAllPartitions with "
                        + "all weights equal to one: every Aⱼ annihilates the orthogonal complement of v. "
                        + "Choose a coordinate i with v(i) nonzero and a summand with Aⱼ(i,i) nonzero. "
                        + "The same owner's supported_column gives column i as z v; transporting back to the joint "
                        + "basis preserves this identity, and the nonzero diagonal entry forces z to be nonzero. "
                        + "That column is a product of local columns; absorbing z⁻¹ into the factor at party zero "
                        + "expresses v itself as a product vector.")),
                    Paragraph(Text(
                        "A Fourier vector g(a,r) cannot be a product vector. Let i and j be the sector strings at "
                        + "t = 0 and t = 1, and let q and p be obtained by swapping their zeroth coordinates. "
                        + "Both original amplitudes are nonzero. Because n and d are at least two, q lies outside "
                        + "the sector and has amplitude zero. A product vector would satisfy "
                        + "v(i)v(j) = v(q)v(p), contradicting these amplitudes. The rank-one argument therefore "
                        + "excludes full separability for every unselected Fourier projector. Consequently an outcome "
                        + "is fully separable exactly when its sector belongs to R.")),
                    Paragraph(Text(
                        "The map sending an outcome b to its zeroth coordinate together with b with that coordinate "
                        + "replaced by zero is a bijection between the selected outcomes and ZMod d times R. "
                        + "There are therefore d times the cardinality of R fully separable operators. "
                        + "The sector labels with zeroth coordinate zero are in bijection with functions from the "
                        + "remaining n − 1 party indices to ZMod d, so there are d^(n − 1) such labels. "
                        + "The bound on m permits a subset R of cardinality m.")),
                    Paragraph(Text(
                        "The local encoding has entry χ(xi) when j = i − y and zero otherwise. Multiplying these "
                        + "entries across parties and acting on g(0,0) gives a scalar of modulus one times g(a,r), "
                        + "where a is the sum of the x inputs and r(k) = y(k) − y(0). The scalar is "
                        + "χ(∑ₖ x(k)(y(k) − y(0))). The winning outcome has precisely this a and r. "
                        + "Conjugation removes the scalar, and the trace against the winning projector is the "
                        + "squared overlap with its selected vector. Fourier orthonormality gives probability one "
                        + "outside R; the computational amplitude has squared modulus 1/d inside R.")),
                    Paragraph(Text(
                        "Reindex y by its zeroth coordinate and its sector label. Exactly d times the cardinality "
                        + "of R of the dⁿ strings have sector in R. The sum of winning probabilities over y is "
                        + "d|R|/d + dⁿ − d|R|, independently of x. Summing over the dⁿ choices of x and dividing "
                        + "by d²ⁿ gives (dⁿ − d|R| + |R|)/dⁿ. With |R| = m, the GHZ density matrix, the clock-shift "
                        + "encodings and the selected projectors satisfy all five conclusions."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tavakoli-abbott-renou-gisin-brunner-2018-multipartite-partial-tightness"),
                    ResolutionKind.Proved)))));

    private static Formula JointIndexFormula() => Dimensions(Equal(
        LocalCall("jointIndex", X("n"), X("d")), Arrow(FinOf(X("n")), Residues())));

    private static Formula WinningOutcomeFormula() => Dimensions(Instances(
        All("x", Joint(), All("y", Joint(), Equal(LocalCall("winningOutcome", X("x"), X("y")),
            LambdaOf("k", FinOf(X("n")), At(Qualified("ite"),
                Equal(X("k"), Typed(D(0), FinOf(X("n")))),
                SumOver("i", FinOf(X("n")), At(X("x"), X("i"))),
                Subtract(At(X("y"), X("k")), At(X("y"), Typed(D(0), FinOf(X("n")))))))))),
        At(Qualified("NeZero"), X("n"))));

    private static Formula ScoreFormula()
    {
        Formula tensor = At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "productMap"),
            At(Qualified("Function", "const"), FinOf(X("n")), Residues()),
            LambdaOf("k", FinOf(X("n")), At(X("u"), X("k"), At(X("x"), X("k")), At(X("y"), X("k")))));
        Formula encoded = Multiply(Multiply(Multiply(tensor, Rho), At(Qualified("Matrix", "conjTranspose"), tensor)),
            At(X("p"), LocalCall("winningOutcome", X("x"), X("y"))));
        Formula body = Multiply(At(Qualified("Inv", "inv"),
                new Formula.Power(CastReal(X("d")), Multiply(Typed(D(2), Naturals()), X("n")))),
            SumOver("x", Joint(), SumOver("y", Joint(), At(Qualified("Complex", "re"),
                At(Qualified("Matrix", "trace"), encoded)))));
        return Dimensions(Instances(All("ρ", JointMatrix(), All("u", Encodings(), All("p", Measurement(),
            Equal(LocalCall("score", Rho, X("u"), X("p")), body)))),
            At(Qualified("NeZero"), X("n")), At(Qualified("NeZero"), X("d")),
            At(Qualified("Fintype"), Joint()), At(Qualified("DecidableEq"), Joint())));
    }

    private static Formula FullySeparableFormula()
    {
        Formula factors = Arrow(FinOf(X("k")), Arrow(FinOf(X("n")), LocalMatrix()));
        Formula positive = All("j", FinOf(X("k")), All("v", FinOf(X("n")),
            At(Qualified("Matrix", "PosSemidef"), At(X("s"), X("j"), X("v")))));
        Formula entries = All("i", Joint(), All("j", Joint(), Equal(At(X("a"), X("i"), X("j")),
            SumOver("q", FinOf(X("k")), ProductOver("v", FinOf(X("n")),
                At(X("s"), X("q"), X("v"), At(X("i"), X("v")), At(X("j"), X("v"))))))));
        return Dimensions(All("a", JointMatrix(), IffOf(LocalCall("IsFullySeparable", X("a")),
            Some("k", Naturals(), Some("s", factors, AndOf(positive, entries))))));
    }

    private static Formula ProjectiveMeasurementFormula() => Dimensions(Instances(All("p", Measurement(),
        IffOf(LocalCall("IsProjectiveMeasurement", X("p")), AndOf(
            All("b", Joint(), At(Qualified("IsStarProjection"), At(X("p"), X("b")))),
            Equal(SumOver("b", Joint(), At(X("p"), X("b"))), Typed(D(1), JointMatrix()))))),
        At(Qualified("NeZero"), X("n")), At(Qualified("NeZero"), X("d")),
        At(Qualified("Fintype"), Joint()), At(Qualified("DecidableEq"), Joint())));

    private static Formula ClaimBody()
    {
        Formula unitary = All("k", FinOf(X("n")), All("x", Residues(), All("y", Residues(),
            new Formula.Relation(At(X("u"), X("k"), X("x"), X("y")), FormulaRelationOperator.MemberOf,
                At(Qualified("Matrix", "unitaryGroup"), Residues(), Complexes())))));
        Formula count = At(Qualified("Finset", "card"), At(Qualified("Finset", "filter"),
            LambdaOf("b", Joint(), LocalCall("IsFullySeparable", At(X("p"), X("b")))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Joint()))));
        Formula value = new Formula.Fraction(
            Add(Subtract(new Formula.Power(CastReal(X("d")), X("n")),
                Multiply(CastReal(X("d")), CastReal(X("m")))), CastReal(X("m"))),
            new Formula.Power(CastReal(X("d")), X("n")));
        Formula conclusions = AndOf(At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), Rho),
            AndOf(unitary, AndOf(LocalCall("IsProjectiveMeasurement", X("p")),
                AndOf(Equal(count, Multiply(X("d"), X("m"))), Equal(LocalCall("score", Rho, X("u"), X("p")), value)))));
        return Dimensions(All("m", Naturals(), Implies(LE(Typed(D(2), Naturals()), X("n")),
            Implies(LE(Typed(D(2), Naturals()), X("d")), Implies(
                LE(X("m"), new Formula.Power(X("d"), Subtract(X("n"), Typed(D(1), Naturals())))),
                Some("ρ", JointMatrix(), Some("u", Encodings(), Some("p", Measurement(), conclusions))))))));
    }

    private static Formula Dimensions(Formula body) => All("n", Naturals(), All("d", Naturals(), body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Residues() => At(Qualified("ZMod"), X("d"));
    private static Formula Joint() => LocalCall("jointIndex", X("n"), X("d"));
    private static Formula JointMatrix() => At(Qualified("Matrix"), Joint(), Joint(), Complexes());
    private static Formula LocalMatrix() => At(Qualified("Matrix"), Residues(), Residues(), Complexes());
    private static Formula Encodings() => Arrow(FinOf(X("n")), Arrow(Residues(), Arrow(Residues(), LocalMatrix())));
    private static Formula Measurement() => Arrow(Joint(), JointMatrix());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula X(string name) => name == "ρ" ? Rho : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "MultipartiteEntangledMeasurementPartialTightness", name);
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
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var instance in instances)
            items.Add(Seq(OpenBracket, instance, CloseBracket, Comma, Sp));
        items.Add(Parenthesized(body));
        return Seq([.. items]);
    }
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula AndOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
