using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class BoseSelectionCubicTwoBathRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/schnellketzmerickeckardt2018bose");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two cubic product-coupled baths admit an open set with five Bose-selected modes.",
        H("Five Bose-selected modes for two cubic baths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("asym"),
                DeclarationHandle.Create(Module + ".asym"),
                H("The two-bath rate asymmetry"),
                StatementSource.FromAuthor(Disp(AsymFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real exponent d, an energy vector ε and two real coupling vectors F and G, "
                        + "asym is the matrix whose (i,j)-entry is the odd power law spow applied to "
                        + "εⱼ − εᵢ, multiplied by the difference of the two normalized product couplings. "
                        + "The declaration D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.spow "
                        + "means |x|ᵈ sgn(x), and the declaration "
                        + "D5/S3/Geometry/FiniteCoordinateTruncation.normalize divides a finite vector "
                        + "by the sum of its coordinates. This is the source's two-bath matrix after the "
                        + "positive factor 2π/ℏ is suppressed, as in main.tex lines 1066–1083."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-selected"),
                DeclarationHandle.Create(Module + ".IsSelected"),
                H("The Bose-selection condition"),
                StatementSource.FromAuthor(Disp(IsSelectedFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "IsSelected a s w says that every index in s has a strictly positive occupation "
                        + "and zero matrix output, while every index outside s has zero occupation and "
                        + "strictly negative matrix output. Here a.mulVec w is the matrix-vector product. "
                        + "The vector w is the source's η. This is the source's MS-problem condition μ = Aη with the selected and unselected "
                        + "sign conditions, main.tex lines 373–381."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("violating"),
                DeclarationHandle.Create(Module + ".violating"),
                H("Parameters with at least four selected modes"),
                StatementSource.FromAuthor(Disp(ViolatingFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For d and m, violating d m is the set of triples of m-component real vectors "
                        + "whose two coupling vectors are positive coordinatewise and for which some "
                        + "finite selected set s and occupation vector w satisfy IsSelected for the "
                        + "matrix asym d ε F G and have cardinality at least four. The three components "
                        + "are the energies and the two coupling vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The generic two-bath bound"),
                StatementSource.FromAuthor(Disp(Equal(Call("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The preregistered generic reading of the source's non-ohmic expectation asks that, "
                        + "for every d > 0 and every natural m, the parameter set supporting at least "
                        + "four selected modes have empty interior. It is the two-bath instance of the "
                        + "proposed bound M_S ≤ 2M_B − 1, corresponding to the source's checked family "
                        + "J(ε) proportional to |ε|ᵈ sgn(ε), main.tex lines 1173–1179."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("An open five-mode counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At d = 3 and m = 5, the referenced odd power law reduces to the cubic map, so "
                            + "asym is skew-symmetric: swapping i and j changes the sign of εⱼ − εᵢ "
                            + "while the product difference is unchanged. For every skew-symmetric 5 by 5 matrix a, "
                            + "the signed Pfaffians of its 4 by 4 principal minors form an explicit vector, "
                            + "and direct expansion gives zero after multiplying a by that vector.")),
                    Paragraph(Text(
                        "On the positive coupling domain, continuous_normalize supplies continuity of each "
                            + "normalized vector because its coordinate sum is positive. The entries of asym and then every "
                            + "coordinate of the Pfaffian vector are therefore continuous. The finite intersection "
                            + "of the positive Pfaffian-coordinate conditions with the positive coupling domain "
                            + "is an open neighborhood.")),
                    Paragraph(Text(
                        "The explicit base point ε = (1,2,3,4,5), F = (5,4,4,4,4), and "
                            + "G = (6,6,3,3,3) belongs to that neighborhood: the five Pfaffian coordinates "
                            + "are positive by exact finite calculation. Every point p in the neighborhood has "
                            + "positive coupling coordinates, and the Pfaffian vector is positive and lies in "
                            + "the kernel of asym 3 p.1 p.2.1 p.2.2. Taking s to be the universal five-element "
                            + "finset and w to be that vector satisfies IsSelected; its cardinality is five, "
                            + "so the neighborhood is contained in violating 3 5.")),
                    Paragraph(Text(
                        "The neighborhood is nonempty because it contains the base point, and its inclusion "
                            + "in violating 3 5 makes the interior of violating 3 5 nonempty. If claim held, its "
                            + "instance at d = 3 and m = 5 would identify that interior with the empty set, "
                            + "contradicting the exhibited point. Hence the generic two-bath bound is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("schnell-ketzmerick-eckardt-2018-bose-selection-cubic-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AsymFormula()
    {
        Formula m = V("m");
        Formula delta = Sub(At(V("ε"), V("j")), At(V("ε"), V("i")));
        Formula products = Sub(
            Mul(Normalize(V("F"), V("i")), Normalize(V("F"), V("j"))),
            Mul(Normalize(V("G"), V("i")), Normalize(V("G"), V("j"))));
        Formula entry = Mul(Spow(V("d"), delta), products);
        Formula body = Equal(Call("asym", V("d"), V("ε"), V("F"), V("G")),
            LambdaOf("i", FinOf(m), LambdaOf("j", FinOf(m), entry)));
        return All("d", Reals(), All("m", Naturals(), All("ε", VectorType(m),
            All("F", VectorType(m), All("G", VectorType(m), body)))));
    }

    private static Formula IsSelectedFormula()
    {
        Formula m = V("m");
        Formula i = V("i");
        Formula selected = Imp(Member(i, V("s")), And(
            LT(RealZero(), At(V("w"), i)),
            Equal(MulVec(V("a"), V("w"), i), RealZero())));
        Formula unselected = Imp(Not(Member(i, V("s"))), And(
            Equal(At(V("w"), i), RealZero()),
            LT(MulVec(V("a"), V("w"), i), RealZero())));
        Formula body = All("i", FinOf(m), And(selected, unselected));
        return All("m", Naturals(), All("a", MatrixType(m), All("s", FinsetType(FinOf(m)),
            All("w", VectorType(m), IffF(Call("IsSelected", V("a"), V("s"), V("w")), body)))));
    }

    private static Formula ViolatingFormula()
    {
        Formula m = V("m");
        Formula p = V("p");
        Formula parameterType = ProdType(VectorType(m), ProdType(VectorType(m), VectorType(m)));
        Formula positiveF = All("i", FinOf(m), LT(RealZero(), At(Fst(Snd(p)), V("i"))));
        Formula positiveG = All("i", FinOf(m), LT(RealZero(), At(Snd(Snd(p)), V("i"))));
        Formula witnesses = Some("s", FinsetType(FinOf(m)), Some("w", VectorType(m), And(
            Call("IsSelected",
                Call("asym", V("d"), Fst(p), Fst(Snd(p)), Snd(Snd(p))), V("s"), V("w")),
            LE(NatNumber(4), Card(V("s"))))));
        Formula predicate = And(positiveF, And(positiveG, witnesses));
        return All("d", Reals(), All("m", Naturals(),
            Equal(Call("violating", V("d"), m), PredicateSet("p", parameterType, predicate))));
    }

    private static Formula ClaimBody() => All("d", Reals(), Imp(
        LT(RealZero(), V("d")), All("m", Naturals(),
            Equal(At(Qualified("interior"), Call("violating", V("d"), V("m"))), Emptyset))));

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "StatisticalMechanics", "BoseSelectionCubicTwoBathRefutation", name);

    private static Formula Call(string name, params Formula[] arguments) => At(Local(name), arguments);

    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
            {
                items.Add(Dot);
            }

            items.Add(F.Id(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula V(string name) => name switch
    {
        "ε" => Varepsilon,
        _ => F.Id(name),
    };

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula VectorType(Formula n) => Arrow(FinOf(n), Reals());
    private static Formula MatrixType(Formula n) => At(Qualified("Matrix"), FinOf(n), FinOf(n), Reals());
    private static Formula FinsetType(Formula type) => At(Qualified("Finset"), type);
    private static Formula ProdType(Formula left, Formula right) => At(Qualified("Prod"), left, right);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula PredicateSet(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(V(name), type), Sp, Bar, Sp, Parenthesized(predicate), CloseBrace);
    private static Formula Fst(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Snd(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula Normalize(Formula vector, Formula index) => At(Qualified(
        "D5", "S3", "Geometry", "FiniteCoordinateTruncation", "normalize"), vector, index);
    private static Formula Spow(Formula exponent, Formula value) => At(Qualified(
        "D5", "S3", "Analytic", "SeriesInequalities", "StampachWaclawekExpansionRefutation", "spow"),
        exponent, value);
    private static Formula MulVec(Formula matrix, Formula vector, Formula index) => At(
        Qualified("Matrix", "mulVec"), matrix, vector, index);
    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula RealZero() => Typed(D(0), Reals());
    private static Formula NatNumber(byte value) => Typed(D(value), Naturals());
    private static Formula Card(Formula value) => At(Qualified("Finset", "card"), value);
}
