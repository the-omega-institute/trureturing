using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class StarGraphEvolutionMapsUnitarilySimilarDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/andradeseverini2018qgraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two evolution maps of every quantum star graph are unitarily similar.",
        H("Unitary similarity of the two star-graph evolution maps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("star-graph-scattering-matrix"),
                DeclarationHandle.Create(Module + ".scatteringMatrix"),
                H("The star-graph scattering matrix"),
                StatementSource.FromAuthor(Disp(ScatteringMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a star with n vertices, the amplitude index is a pair consisting of "
                        + "an edge in Fin (n − 1) and a direction in Fin 2. At an edge index p, "
                        + "an incoming direction zero scatters only to the reverse direction at "
                        + "the same edge with amplitude r. An incoming direction one scatters "
                        + "to direction zero, with amplitude r1 on the same edge and t1 on every "
                        + "other edge. This is the matrix displayed for Sₙ in the source at TeX "
                        + "lines 383–405."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("star-graph-propagation-matrix"),
                DeclarationHandle.Create(Module + ".propagationMatrix"),
                H("The diagonal propagation matrix"),
                StatementSource.FromAuthor(Disp(PropagationMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every amplitude on the edge indexed by p is multiplied by the same phase "
                        + "exp(I k ℓ(p.1)). The real wave number k and edge length ℓ(p.1) enter "
                        + "the complex exponential through Complex.ofReal. Thus the diagonal "
                        + "entries are the edge factors zᵢⱼ = exp(i k ℓᵢⱼ) described at TeX line "
                        + "298 and in the star-graph construction at lines 383–405."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("star-graph-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The universal unitary-similarity claim"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every star size n at least two, every complex collection of edge "
                        + "reflection amplitudes, every pair of complex central amplitudes, every "
                        + "real wave number and every real edge-length function, there is a unitary "
                        + "matrix w that conjugates scatteringMatrix times propagationMatrix to "
                        + "propagationMatrix times scatteringMatrix. This is the repository's "
                        + "formal reading of Claim 1, which the source states at TeX lines 522–530."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("star-graph-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The propagation matrix is the conjugating unitary"),
                StatementSource.FromAuthor(Disp(LocalCall("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n, the amplitudes, the wave number and the edge lengths in the "
                            + "quantified claim. Write D for propagationMatrix k ℓ and S for "
                            + "scatteringMatrix r r1 t1. Each diagonal entry of D has norm one: "
                            + "the real exponential phase calculation gives ‖exp(I k ℓ(p.1))‖ = 1.")),
                    Paragraph(Text(
                        "The diagonal-unitary criterion then proves that D belongs to the unitary "
                            + "group. Regard D as a unit in the matrix ring. Its inverse is its "
                            + "star, so multiplying the identity D D⁻¹ = 1 on the right of D S "
                            + "gives D (S D) star(D) = D S.")),
                    Paragraph(Text(
                        "Choose w = D. The preceding unitary membership and conjugation identity "
                            + "supply the two witnesses required by the existential statement, "
                            + "which proves the claim for every n and all the quantified data."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ScatteringMatrixFormula()
    {
        Formula n = X("n"), r = X("r"), r1 = X("r1"), t1 = X("t1");
        Formula p = X("p"), q = X("q");
        Formula pFirst = At(Qualified("Prod", "fst"), p);
        Formula pSecond = At(Qualified("Prod", "snd"), p);
        Formula qFirst = At(Qualified("Prod", "fst"), q);
        Formula qSecond = At(Qualified("Prod", "snd"), q);
        Formula zeroFin2 = Typed(D(0), Fin(D(2)));
        Formula oneFin2 = Typed(D(1), Fin(D(2)));
        Formula zeroComplex = Typed(D(0), Complexes);
        Formula sameEdgeReverse = And(Eq(qFirst, pFirst), Eq(qSecond, oneFin2));
        Formula firstBranch = Ite(sameEdgeReverse, At(r, pFirst), zeroComplex);
        Formula secondBranch = Ite(Eq(qSecond, oneFin2), zeroComplex,
            Ite(Eq(qFirst, pFirst), r1, t1));
        Formula value = Ite(Eq(pSecond, zeroFin2), firstBranch, secondBranch);
        return All("n", Naturals, All("r", Arrow(Fin(Sub(n, D(1))), Complexes),
            All("r1", Complexes, All("t1", Complexes,
                All("p", IndexType(n), All("q", IndexType(n),
                    Eq(Typed(LocalCall("scatteringMatrix", r, r1, t1, p, q), MatrixType(n)),
                        value)))))));
    }

    private static Formula PropagationMatrixFormula()
    {
        Formula n = X("n"), k = X("k"), ell = X("ℓ"), p = X("p");
        Formula phase = Call("Complex.exp",
            Mul(Mul(Call("Complex.I"), Call("Complex.ofReal", k)),
                Call("Complex.ofReal", At(ell, At(Qualified("Prod", "fst"), p)))));
        Formula diagonal = At(Qualified("Matrix", "diagonal"),
            LambdaOf("p", IndexType(n), phase));
        return All("n", Naturals, All("k", Reals, All("ℓ", Arrow(Fin(Sub(n, D(1))), Reals),
            Eq(Typed(LocalCall("propagationMatrix", k, ell), MatrixType(n)), diagonal))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = X("n"), r = X("r"), r1 = X("r1"), t1 = X("t1");
        Formula k = X("k"), ell = X("ℓ"), w = X("w");
        Formula index = IndexType(n);
        Formula matrix = MatrixType(n);
        Formula unitary = Call("Matrix.unitaryGroup", index, Complexes);
        Formula left = Mul(Mul(w,
            Mul(LocalCall("scatteringMatrix", r, r1, t1),
                LocalCall("propagationMatrix", k, ell))),
            Call("star", w));
        Formula right = Mul(LocalCall("propagationMatrix", k, ell),
            LocalCall("scatteringMatrix", r, r1, t1));
        Formula witness = Some("w", matrix, And(Mem(w, unitary), Eq(left, right)));
        Formula quantified = All("n", Naturals, Imp(Le(Typed(D(2), Naturals), n),
            All("r", Arrow(Fin(Sub(n, D(1))), Complexes),
                All("r1", Complexes, All("t1", Complexes, All("k", Reals,
                    All("ℓ", Arrow(Fin(Sub(n, D(1))), Reals), witness)))))));
        return Eq(LocalCall("claim"), quantified);
    }

    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Qualified("D5", "S3", "Quantum", "Transport",
            "StarGraphEvolutionMapsUnitarilySimilar", name), arguments);

    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula X(string name) => name == "ℓ" ? Ell : F.Id(name);

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        At(Qualified(name.Split('.')), arguments);

    private static Formula LocalCall(string name, Formula a, Formula b, Formula c, Formula d, Formula e) =>
        At(Qualified("D5", "S3", "Quantum", "Transport",
            "StarGraphEvolutionMapsUnitarilySimilar", name), a, b, c, d, e);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula IndexType(Formula n) =>
        Call("Prod", Fin(Sub(n, D(1))), Fin(D(2)));

    private static Formula MatrixType(Formula n) =>
        Call("Matrix", IndexType(n), IndexType(n), Complexes);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));

    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Ite(Formula condition, Formula whenTrue, Formula whenFalse) =>
        Call("ite", condition, whenTrue, whenFalse);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
