using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class OverlapIntervalPropagationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/galvaobrod2020overlaps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five overlaps of four pure states force the sixth to be one quarter, although intersection of the three-state lower bounds gives zero.",
        H("Three-state overlap intervals need not be tight"),
        Blocks(
            Node("upper", "The three-state upper bound", UpperFormula(),
                "For real x and y, upper is the square of the sum of the two square roots. "
                    + "For known pure-state overlaps in the unit interval, this is the upper bound in overlap_pra_v3.tex, lines 118–122. "
                    + "The definition is a total real function and does not assume that its arguments lie in that interval.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lower", "The three-state lower bound", LowerFormula(),
                "The lower bound is the square of the difference of the two square roots when x + y is strictly greater than one, "
                    + "and zero otherwise, including x + y = 1. This is the piecewise bound in overlap_pra_v3.tex, lines 125–131, "
                    + "extended as a total function on all real arguments.",
                AssessedProvenance.FromLiterature(Source)),
            Node("overlap", "Squared overlap of two vectors", OverlapFormula(),
                "The overlap is the squared norm of the complex inner product of u and v in the n-dimensional complex Euclidean space. "
                    + "For unit vectors this is the pure-state overlap of overlap_pra_v3.tex, lines 97–102. "
                    + "The definition itself imposes no normalization condition and includes dimension zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("realizes", "Realizing the given pairs", RealizesFormula(),
                "A family ψ realizes the given values when each vector has norm one and every ordered pair of distinct indices "
                    + "has overlap r i j, except when its unordered two-element finite set equals the unknown pair. "
                    + "Thus both orientations of the unknown pair are omitted, and diagonal values of r impose no conditions. "
                    + "The predicate permits arbitrary n, m, i₀, j₀ and r, without separately requiring symmetry of r or distinctness of i₀ and j₀.",
                AssessedProvenance.FromRepo(Source)),
            Node("feasible", "All feasible values of the unknown overlap", FeasibleFormula(),
                "The feasible set consists of the real values t realized as the unknown squared overlap by some normalized family "
                    + "satisfying every given pair. Both the natural dimension n and the family ψ are existentially quantified, "
                    + "so no fixed dimension is assumed.",
                AssessedProvenance.FromRepo(Source)),
            Node("procLower", "Intersection of the lower bounds", ProcedureFormula("procLower", "sSup", "lower"),
                "For every k distinct from i₀ and j₀, apply the three-state lower bound to r k i₀ and r k j₀, "
                    + "then take the supremum of the resulting set. This is the lower endpoint of the common-neighbour intersection "
                    + "in overlap_pra_v3.tex, lines 151–154, for a graph with only the pair i₀,j₀ unknown. "
                    + "For m at least three the finite set is nonempty and its supremum is its maximum. "
                    + "The definition also includes smaller m through the real supremum operation.",
                AssessedProvenance.FromLiterature(Source)),
            Node("procUpper", "Intersection of the upper bounds", ProcedureFormula("procUpper", "sInf", "upper"),
                "Apply the three-state upper bound through each common neighbour k and take the infimum of those values. "
                    + "This is the upper endpoint of the intersection in overlap_pra_v3.tex, lines 151–154, for one unknown pair. "
                    + "For m at least three the finite nonempty set has a minimum; the definition uses the real infimum operation for every m.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Universal tightness with one unknown pair", ClaimFormula(),
                "For every m at least three, every pair of distinct indices i₀,j₀ and every given array r with a nonempty feasible set, "
                    + "claim asserts that procLower equals the feasible infimum and procUpper equals the feasible supremum. "
                    + "This formulates tightness for the case of one unknown pair in the optimality question of overlap_pra_v3.tex, line 165. "
                    + "All other pairs are already given, so revisiting the unknown pair uses the same common-neighbour bounds. "
                    + "The statement concerns pure states in arbitrary finite dimension.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("overlap-interval-propagation-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four pure states contradict universal tightness"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take m = 4, i₀ = 2 and j₀ = 3. Let the rows of r be (1,0,1/2,1/2), (0,1,1/2,0), "
                            + "(1/2,1/2,1,0) and (1/2,0,0,1). The entries at the unknown pair impose no condition. "
                            + "The two common neighbours are 0 and 1. Through 0 the lower bound is lower (1/2) (1/2) = 0, "
                            + "because the sum equals one; through 1 it is lower (1/2) 0 = 0. "
                            + "The set defining procLower is therefore the singleton containing zero, and procLower 4 2 3 r = 0.")),
                    Paragraph(Text(
                        "Put q = √(1/2) and choose ψ 0 = (1,0,0), ψ 1 = (0,1,0), ψ 2 = (q,q,0) and ψ 3 = (q,0,q) "
                            + "in complex Euclidean dimension three, including each real q as a complex scalar. "
                            + "Since q² = 1/2 and its complex norm squared is also 1/2, summing squared coordinate norms gives norm one for every vector. "
                            + "Expanding each inner product as the sum of the three conjugate-coordinate products gives "
                            + "overlap (ψ 0) (ψ 1) = 0, overlap (ψ 0) (ψ 2) = overlap (ψ 0) (ψ 3) = overlap (ψ 1) (ψ 2) = 1/2, "
                            + "and overlap (ψ 1) (ψ 3) = 0, with the same values in reverse order. Thus this family realizes r.")),
                    Paragraph(Text(
                        "Next let a, b and c be unit vectors in any finite complex Euclidean dimension, with overlap a b = 0 "
                            + "and overlap a c = overlap b c = 1/2. The zero squared norm of the inner product of a and b makes them orthogonal. "
                            + "Set p = ⟨a,c⟩ a + ⟨b,c⟩ b, using the inner product linear in its second argument. "
                            + "The two summands are orthogonal, and their squared norms add to 1/2 + 1/2 = 1, so the squared norm of p is one. "
                            + "Conjugate symmetry also gives Re ⟨c,p⟩ = |⟨a,c⟩|² + |⟨b,c⟩|² = 1. "
                            + "The equality criterion relating the norm and the real inner product, together with the unit norm of c, gives c = p.")),
                    Paragraph(Text(
                        "Apply this identity to a = ψ 0, b = ψ 1 and c = ψ 2 in an arbitrary realization, and put d = ψ 3. "
                            + "The given zero overlap of b and d gives ⟨b,d⟩ = 0. Expanding the first argument using c = ⟨a,c⟩ a + ⟨b,c⟩ b "
                            + "therefore gives ⟨c,d⟩ = conjugate(⟨a,c⟩) ⟨a,d⟩. "
                            + "Multiplicativity of the complex norm and invariance under conjugation yield "
                            + "overlap c d = |⟨a,c⟩|² |⟨a,d⟩|² = (1/2)(1/2) = 1/4.")),
                    Paragraph(Text(
                        "The explicit family in dimension three makes the feasible set nonempty. The identity just proved shows that every feasible value is 1/4, "
                            + "and the explicit family attains that value. Hence the feasible set is the singleton containing 1/4, whose infimum is 1/4. "
                            + "If claim held, its lower-endpoint equality at m = 4, i₀ = 2, j₀ = 3 and this r would give 0 = 1/4, a contradiction. "
                            + "This already disproves the conjunction of endpoint equalities without computing procUpper."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("galvao-brod-2020-overlap-interval-propagation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("overlap-interval-propagation-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula UpperFormula() => All("x", Reals(), All("y", Reals(),
        Equal(Typed(LocalCall("upper", X("x"), X("y")), Reals()),
            Square(Add(Root(Mul(X("x"), X("y"))), Root(ComplementProduct()))))));

    private static Formula LowerFormula() => All("x", Reals(), All("y", Reals(),
        Equal(Typed(LocalCall("lower", X("x"), X("y")), Reals()),
            At(Qualified("ite"), Parenthesized(Less(R(1), Add(X("x"), X("y")))),
                Square(Subtract(Root(Mul(X("x"), X("y"))), Root(ComplementProduct()))), R(0)))));

    private static Formula ComplementProduct() =>
        Mul(Subtract(R(1), X("x")), Subtract(R(1), X("y")));

    private static Formula OverlapFormula() => All("n", Naturals(), All("u", Vectors(), All("v", Vectors(),
        Equal(Typed(LocalCall("overlap", X("u"), X("v")), Reals()),
            Square(new Formula.Norm(At(Qualified("inner"), Complexes(), X("u"), X("v"))))))));

    private static Formula RealizesFormula()
    {
        Formula normalized = All("k", FinOf(X("m")), Equal(new Formula.Norm(At(X("ψ"), X("k"))), R(1)));
        Formula pairs = All("i", FinOf(X("m")), All("j", FinOf(X("m")),
            Arrow(NotEqual(X("i"), X("j")),
                Arrow(NotEqual(PairSet(X("i"), X("j")), PairSet(X("i₀"), X("j₀"))),
                    Equal(LocalCall("overlap", At(X("ψ"), X("i")), At(X("ψ"), X("j"))),
                        At(X("r"), X("i"), X("j")))))));
        return All("n", Naturals(), InstanceBinders(All("ψ", Family(),
            Equivalence(LocalCall("realizes", X("i₀"), X("j₀"), X("r"), X("ψ")), Conjunction(normalized, pairs)))));
    }

    private static Formula FeasibleFormula()
    {
        Formula condition = Some("n", Naturals(), Some("ψ", Family(),
            Conjunction(LocalCall("realizes", X("i₀"), X("j₀"), X("r"), X("ψ")),
                Equal(X("t"), LocalCall("overlap", At(X("ψ"), X("i₀")), At(X("ψ"), X("j₀")))))));
        return InstanceBinders(Equal(Typed(Feasible(), At(Qualified("Set"), Reals())), RealSet(condition)));
    }

    private static Formula ProcedureFormula(string declaration, string extremum, string bound)
    {
        Formula condition = Some("k", FinOf(X("m")), Conjunction(NotEqual(X("k"), X("i₀")),
            Conjunction(NotEqual(X("k"), X("j₀")),
                Equal(X("t"), LocalCall(bound, At(X("r"), X("k"), X("i₀")), At(X("r"), X("k"), X("j₀")))))));
        return InstanceBinders(Equal(Typed(LocalCall(declaration, X("m"), X("i₀"), X("j₀"), X("r")), Reals()),
            At(Qualified(extremum), RealSet(condition))));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), InstanceBinders(
        Arrow(new Formula.Relation(Typed(D(3), Naturals()), FormulaRelationOperator.LessThanOrEqual, X("m")),
            Arrow(NotEqual(X("i₀"), X("j₀")), Arrow(At(Qualified("Set", "Nonempty"), Feasible()),
                Conjunction(Equal(LocalCall("procLower", X("m"), X("i₀"), X("j₀"), X("r")),
                        At(Qualified("sInf"), Feasible())),
                    Equal(LocalCall("procUpper", X("m"), X("i₀"), X("j₀"), X("r")),
                        At(Qualified("sSup"), Feasible()))))))));

    private static Formula InstanceBinders(Formula body) => All("m", Naturals(),
        All("i₀", FinOf(X("m")), All("j₀", FinOf(X("m")), All("r", GivenArray(), body))));
    private static Formula Feasible() => LocalCall("feasible", X("m"), X("i₀"), X("j₀"), X("r"));
    private static Formula GivenArray() => Arrow(FinOf(X("m")), Arrow(FinOf(X("m")), Reals()));
    private static Formula Family() => Arrow(FinOf(X("m")), Vectors());
    private static Formula Vectors() => At(Qualified("EuclideanSpace"), Complexes(), FinOf(X("n")));
    private static Formula PairSet(Formula a, Formula b) => Typed(
        Seq(OpenBrace, a, Comma, Sp, b, CloseBrace), At(Qualified("Finset"), FinOf(X("m"))));
    private static Formula RealSet(Formula condition) =>
        Seq(OpenBrace, Typed(X("t"), Reals()), Sp, Mid, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "PureState", "OverlapIntervalPropagationRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name switch
    {
        "ψ" => Psi,
        "i₀" => new Formula.Subscript(F.Id("i"), D(0)),
        "j₀" => new Formula.Subscript(F.Id("j"), D(0)),
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
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R(byte value) => Typed(D(value), Reals());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Root(Formula value) => At(Qualified("Real", "sqrt"), value);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Typed(D(2), Naturals()));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
