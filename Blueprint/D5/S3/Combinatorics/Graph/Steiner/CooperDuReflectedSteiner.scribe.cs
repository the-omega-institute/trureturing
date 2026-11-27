using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Steiner;

internal sealed class CooperDuReflectedSteinerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/cooperdu2025steinerdistancehypermatrices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The star with 47 leaves has a negative real H-eigenvalue for the last-reflected Steiner form at every even order at least four.",
        H("Negative H-eigenvalues of reflected Steiner forms"),
        Blocks(
            Definition("steinerEntry", "Steiner distance of an ordered tuple", EntryFormula(),
                "On printed page 1, Cooper and Du define Steiner distance by minimizing the number of edges in a connected subgraph containing all the specified vertices. In a tree the minimum is the size of the unique minimal subtree spanning those vertices. An ordered tuple may repeat vertices, so repetitions constrain the same vertex and add no edges. The subgraph H is a connected subgraph of G and |E(H)| counts its undirected edges once. The proof h of connectedness of G ensures the minimum exists.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("steinerForm", "Steiner multilinear form", FormFormula(),
                "The sum on printed page 1 ranges over all ordered k-tuples of vertices, including repeated indices. There is one coordinate factor from each input slot, and the natural edge count is cast to a real coefficient.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("reflect", "Reflection through the all-ones line", ReflectionFormula(),
                "Lemma 4.2 on printed page 8 gives the reflection through the span of the all-ones vector. The term twice the mean is the same at every vertex. The map fixes constant vectors and reverses vectors with coordinate sum zero.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("reflectedRow", "First-slot contraction of the last-reflected form", RowFormula(),
                "Printed page 9 defines C₁ at order four by applying the reflection in the last slot of the Steiner form. The same placement defines the higher-order form here. The slot vector z starts with the vertex basis vector eᵢ, followed by m copies of the real vector x and then the reflected x. The order is m + 2.",
                AssessedProvenance.FromRepo(Source)),
            Definition("IsHEigenpair", "Real H-eigenpair equations", EigenpairFormula(),
                "The vector x is real and nonzero, and lam is real. Each first-slot row equals the eigenvalue times the corresponding coordinate raised to the power m + 1, which is one less than the tensor order.",
                AssessedProvenance.FromRepo(Source)),
            Definition("claim", "Cooper and Du’s positivity question", ClaimFormula(),
                "After Proposition 4.5 on printed page 10, Cooper and Du ask whether the H-eigenvalues of C₁ are all positive and whether this extends to all even orders. The proposition requires strict positivity for every real H-eigenpair on every finite simple tree with at least three vertices at each even order k at least four. The tree proof hG supplies the connectedness argument. Relabelling the paper’s vertices by Fin n preserves both the Steiner entries and the eigenpair equations.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("cooper-du-star-negative"), DeclarationHandle.Create(Prefix + "star_negative"),
                H("A fixed star gives a negative H-eigenvalue at every even order at least four"),
                StatementSource.FromAuthor(StarNegativeFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Cooper and Du’s last-slot reflection and positivity question motivate this construction. For each natural even order k ≥ 4, the theorem gives a nonzero real vector x on the same star K₁,₄₇ with centre 0 on Fin 48 and a real eigenvalue lam < 0. The eigenpair may depend on k. In the formula, hStar is (isTree_starGraph (0 : Fin 48)).connected. The first-slot contraction has k − 2 copies of x between the basis vector and the reflected x.")),
                    Paragraph(Text(
                        "On the star with 47 leaves, the minimal subtree uses exactly the leaf edges whose cuts the tuple crosses. In the multilinear sum, each cut contributes the product of the whole-vertex slot sums minus the two products of slot sums restricted to its sides. Give all leaves coordinate −1 and the centre coordinate s + 47. The contraction then has a single centre value and a common leaf value.")),
                    Paragraph(Text(
                        "Eliminating the eigenvalue from the two row equations gives a continuous polynomial in s. It is positive at 24/23 and negative at 2 for every even order k at least four. The intermediate value theorem gives a zero. There the contribution from a leaf’s own cut is positive, so the balance forces the common contribution from the other cuts to be negative. The centre equation gives a negative eigenvalue, and the balance equation gives the leaf equation.")),
                    Paragraph(Text(
                        "The corresponding Reg registration is Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.registration. Its parameter coordinates are k followed by x, its real state is lam, and its Boolean readout decides the displayed IsHEigenpair predicate. The registration law retains the two premises on k, the two existential binders, and lam < 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cooper-du-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The order-four instance refutes claim"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Apply star_negative at k = 4. The star on Fin 48 satisfies the size and tree hypotheses of claim, which would make the supplied eigenvalue strictly positive. The witness has a strictly negative eigenvalue, giving ¬ claim."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("cooper-du-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vertices() => Call("Fin", F.Id("n"));
    private static Formula VectorType() => Seq(Vertices(), Sp, To, Sp, Reals());

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);

    private static Formula EntryFormula()
    {
        Formula h = F.Id("h"), t = F.Id("t"), subgraph = F.Id("H");
        Formula contains = All("a", Call("Fin", F.Id("k")),
            Seq(Call("t", F.Id("a")), Sp, InMacro, Sp, Call("V", subgraph)));
        Formula admissible = Seq(subgraph, Sp, Subseteq, Sp, F.Id("G"), Comma, Sp,
            Seq(subgraph, Dot, F.Id("Connected")), Comma, Sp, contains);
        Formula minimum = Seq(Min, Sp, OpenBrace, Sp,
            new Formula.Absolute(Call("E", subgraph)), Sp, Mid, Sp, admissible, Sp, CloseBrace);
        return Disp(Equal(Call("steinerEntry", h, t), minimum));
    }

    private static Formula FormFormula()
    {
        Formula h = F.Id("h"), t = F.Id("t"), a = F.Id("a"), z = F.Id("z");
        Formula slots = Call("Fin", F.Id("k"));
        Formula coordinate = new Formula.Apply(Seq(z, Underscore, Grp(a)), [Call("t", a)]);
        Formula factors = Seq(Prod, Underscore, Grp(Seq(a, Sp, Colon, Sp, slots)), Sp, coordinate);
        Formula term = Seq(Call("steinerEntry", h, t), Sp, Cdot, Sp, factors);
        Formula tuples = Grp(Seq(t, Sp, Colon, Sp, slots, Sp, To, Sp, Vertices()));
        return Disp(Equal(Call("steinerForm", h, z), Seq(Sum, Underscore, tuples, Sp, term)));
    }

    private static Formula ReflectionFormula()
    {
        Formula x = F.Id("x"), i = F.Id("i"), j = F.Id("j");
        Formula sum = Seq(Sum, Underscore, Grp(Seq(j, Sp, Colon, Sp, Vertices())), Sp, Call("x", j));
        Formula twiceMean = new Formula.Fraction(Seq(D(2), Sp, sum), F.Id("n"));
        return Disp(Equal(Call("reflect", x, i), Seq(twiceMean, Sp, Minus, Sp, Call("x", i))));
    }

    private static Formula RowFormula()
    {
        Formula h = F.Id("h"), m = F.Id("m"), x = F.Id("x"), i = F.Id("i"), z = F.Id("z");
        Formula basis = Seq(F.Id("e"), Underscore, Grp(i));
        Formula copies = Seq(Parenthesized(x), Underscore,
            Grp(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin", m))));
        Formula slots = Parenthesized(Seq(basis, Comma, Sp, copies, Comma, Sp, Call("reflect", x)));
        return Disp(Seq(Equal(Call("reflectedRow", h, m, x, i), Call("steinerForm", h, z)),
            Comma, Quad, Equal(z, slots)));
    }

    private static Formula EigenpairFormula()
    {
        Formula h = F.Id("h"), m = F.Id("m"), x = F.Id("x"), i = F.Id("i");
        Formula lam = F.Id("lam");
        Formula nonzero = new Formula.Relation(x, FormulaRelationOperator.NotEqual, D(0));
        Formula exponent = Seq(m, Sp, Plus, Sp, D(1));
        Formula coordinatePower = new Formula.Power(Call("x", i), exponent);
        Formula row = All("i", Vertices(), Equal(Call("reflectedRow", h, m, x, i),
            Seq(lam, Sp, Cdot, Sp, coordinatePower)));
        Formula equations = new Formula.Logic(nonzero, FormulaLogicOperator.And, Parenthesized(row));
        return Disp(new Formula.Logic(Call("IsHEigenpair", h, m, x, lam),
            FormulaLogicOperator.Iff, Parenthesized(equations)));
    }

    private static Formula StarNegativeFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), lam = F.Id("lam");
        Formula vertices = Call("Fin", D(4, 8));
        Formula vectorType = Seq(vertices, Sp, To, Sp, Reals());
        Formula connected = F.Id("hStar");
        Formula m = Parenthesized(Seq(k, Sp, Minus, Sp, D(2)));
        Formula pair = Call("IsHEigenpair", connected, m, x, lam);
        Formula negative = new Formula.Relation(lam, FormulaRelationOperator.LessThan, D(0));
        Formula condition = new Formula.Logic(negative, FormulaLogicOperator.And, pair);
        Formula witness = Seq(Exists, Sp,
            Parenthesized(Seq(x, Sp, Colon, Sp, vectorType)), Sp,
            Parenthesized(Seq(lam, Sp, Colon, Sp, Reals())), Comma, Sp, condition);
        Formula hypotheses = Seq(D(4), Sp, Leq, Sp, k, Sp, Rightarrow, Sp,
            Call("Even", k), Sp, Rightarrow, Sp, witness);
        return Disp(All("k", Naturals(), hypotheses));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), g = F.Id("G"), tree = F.Id("hG"), lam = F.Id("lam");
        Formula connected = Seq(tree, Dot, F.Id("connected"));
        Formula m = Parenthesized(Seq(k, Sp, Minus, Sp, D(2)));
        Formula pair = Call("IsHEigenpair", connected, m, F.Id("x"), lam);
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, lam);
        Formula conclusion = Seq(pair, Sp, Rightarrow, Sp, positive);
        Formula trees = All("G", Call("SimpleGraph", Vertices()),
            All("hG", Seq(g, Dot, F.Id("IsTree")),
                All("x", VectorType(), All("lam", Reals(), conclusion))));
        Formula hypotheses = Seq(D(3), Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            D(4), Sp, Leq, Sp, k, Sp, Rightarrow, Sp, Call("Even", k), Sp, Rightarrow, Sp,
            Parenthesized(trees));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All("n", Naturals(), All("k", Naturals(), hypotheses)))));
    }
}
