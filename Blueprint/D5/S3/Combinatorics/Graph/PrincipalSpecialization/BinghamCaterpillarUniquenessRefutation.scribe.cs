using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrincipalSpecialization;

internal sealed class BinghamCaterpillarUniquenessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/bingham2026principalspecializations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eighteen-vertex caterpillars (2,2,2,2,2,1,4,3) and (2,2,3,2,3,4,2) refute the second, exhaustive-pairs question in Remark 3.11.",
        H("A counterexample to the exhaustive-pairs assertion"), Blocks(
            Node("admissible", "The entire source domain", "admissible", Admissible(),
                "The entries of a are positive naturals indexed by Fin l. The first disjunct is the singleton (1). The second allows every nonempty length whose first and last parts are at least two, including length-one stars. For length one the same part is both endpoints. Positive entries and the endpoint condition imply total size at least two. This is Definition 2.1; Lemma 2.2 is not needed."),
            Node("ordinary", "The actual ordinary specialization over C", "ordinary", Ordinary(),
                "G is any finite simple graph on V. The sum includes every proper coloring into Fin k, without surjectivity. Equation (2.1) changes the color names to 0 through k−1; the exponent is the sum over all actual vertices. The proof establishes ordinary G k = Polynomial.map (Int.castRingHom C) (ps G k), with ps reused from BinghamCaterpillarPs3Family. Polynomial.map_injective and Int.cast_injective prove that equality of these complex polynomials is equivalent to equality of the integer coloring-count polynomials. No numerical evaluation or t refinement is involved."),
            Node("pair", "Unordered graph-isomorphism pairs", "pairIso", PairIso(),
                "Iso(a,c) abbreviates Nonempty (caterpillar a ≃g caterpillar c). The carrier and edge relation are the original Vertex and caterpillar definitions from BinghamCaterpillarPs3Family: a spine path with val(a(i))−1 attached leaves. Graph isomorphisms allow arbitrary relabeling, so this relation includes reversals and both pair orders. No classification of graph isomorphisms by reversed compositions is assumed."),
            Node("base-a", "The first base member", "baseA", Eq(Call("baseA"), Tuple(5,4,3)),
                "The base pair displayed in Remark 3.11."),
            Node("base-b", "The second base member", "baseB", Eq(Call("baseB"), Tuple(4,5,3)),
                "Both base compositions have three spine vertices."),
            Node("listed", "All listed exceptions", "listed", Listed(),
                "The positive natural j has no upper bound; alpha(j)=(5,j,j,4,3) and beta(j)=(4,j,j,5,3) are reused from the first-question module. In particular j=1 remains included. Pair isomorphism takes the full unordered isomorphism closure of the base and every family pair."),
            Node("claim", "Remark 3.11, the whole second assertion", "claim", Iff(Id("claim"), ClaimBody()),
                "n ranges over every natural number at least one; la and lb are arbitrary natural lengths. The two compositions are source-admissible and each has total size n. If their ordinary second polynomials differ and third polynomials agree identically, the assertion says their unordered graph-isomorphism pair is listed. The base exception and every positive-j family are included. This is an assertion over all sizes, not a finite search bound."),
            Node("a", "The first witness", "witnessA", Eq(Call("witnessA"),Tuple(2,2,2,2,2,1,4,3)),
                "The eight positive parts sum to eighteen and both endpoints are at least two. The internal part one has no attached leaves; its spine vertex still has its two spine neighbors."),
            Node("b", "The second witness", "witnessB", Eq(Call("witnessB"),Tuple(2,2,3,2,3,4,2)),
                "The seven positive parts sum to eighteen and satisfy the same endpoint condition."),
            Describe.Lean(DescribeId.Create("bingham-uniqueness-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The exhaustive-pairs assertion is false"), StatementSource.FromAuthor(Disp(Seq(Neg,Id("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For A=witnessA and B=witnessB, the actual two-color polynomials are X^8+X^10 and 2X^9. The coefficients at degree eight are one and zero. Their actual three-color polynomials agree. The proof directly reuses ps_spine_sum, which follows from the original explicit bijection between all proper colorings and proper spine colorings with independent leaf choices. Each block has weight X^c times (the sum of X^d over d different from c) to the power val(a(i))−1. Finite spine sums and polynomial normalization prove the two identities and the complete third-polynomial equality. The injective coefficient-extension bridge transfers both comparisons to the source's complex polynomials. To exclude every listed pair, a vertex with two distinct neighbors must lie on the spine: a pendant vertex has its incident spine vertex as its only neighbor. Every one of A's eight spine vertices has two distinct neighbors. Any graph isomorphism from A to a caterpillar with l spine vertices would therefore induce an injection Fin 8 into Fin l. Each base member has l=3 and each family member has l=5 for every positive j. The resulting cardinal inequalities exclude every such isomorphism, including all relabelings, reversals, and pair exchanges. This single pair refutes the full universal assertion. It asserts no minimality, priority, converse classification, four-color statement, or t-refined extension."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bingham-2026-caterpillar-principal-specialization-uniqueness"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("bingham-uniqueness-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Id(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Nat() => Seq(Mathbb,Grp(Id("N")));
    private static Formula Positive() => new Formula.Power(Nat(),Plus);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname,Grp(Id(name))) : new Formula.Apply(Seq(Operatorname,Grp(Id(name))),[..args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall,Sp,P(Seq(Id(name),Colon,type)),Comma,Sp,body);
    private static Formula Exists(string name, Formula type, Formula body) => Seq(F.Exists,Sp,P(Seq(Id(name),Colon,type)),Comma,Sp,body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.And,P(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.Or,P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.Iff,P(y));
    private static Formula Implies(Formula x, Formula y) => Seq(P(x),Sp,Rightarrow,Sp,P(y));
    private static Formula Tuple(params byte[] xs) => Seq(Bang,OpenBracket,Joined(xs),CloseBracket);
    private static Formula Joined(byte[] xs)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var x in xs) { if (items.Count != 0) items.Add(Comma); items.Add(D(x)); }
        return Seq([..items]);
    }
    private static Formula Admissible() => All("l",Nat(),All("a",Call("Parts",Id("l")),Iff(Call("admissible",Id("a")),
        Or(And(Eq(Id("l"),D(1)),All("i",Call("Fin",Id("l")),Eq(Call("a",Id("i")),D(1)))),
            And(Le(D(1),Id("l")),All("i",Call("Fin",Id("l")),Implies(
                Or(Eq(Call("val",Id("i")),D(0)),Eq(new Formula.Binary(Call("val",Id("i")),FormulaBinaryOperator.Add,D(1)),Id("l"))),
                Le(D(2),Call("val",Call("a",Id("i")))))))))));
    private static Formula Ordinary() => All("V",Seq(Id("Type"),Star),Seq(OpenBracket,Call("Fintype",Id("V")),CloseBracket,Sp,
        All("G",Call("SimpleGraph",Id("V")),All("k",Nat(),Eq(Call("ordinary",Id("G"),Id("k")),
            Seq(new Formula.Subscript(F.Sum,Seq(Id("c"),Colon,Call("Coloring",Id("G"),Call("Fin",Id("k"))))),Sp,
                new Formula.Power(Id("X"),Seq(new Formula.Subscript(F.Sum,Seq(Id("v"),Colon,Id("V"))),Sp,Call("val",Call("c",Id("v")))))))))));
    private static Formula Iso(string a, string b) => Call("Iso",Id(a),Id(b));
    private static Formula PairIso()
    {
        Formula body = Iff(Call("pairIso",Id("a"),Id("b"),Id("c"),Id("d")),
            Or(And(Iso("a","c"),Iso("b","d")),And(Iso("a","d"),Iso("b","c"))));
        body = All("d",Call("Parts",Id("ld")),body);
        body = All("c",Call("Parts",Id("lc")),body);
        body = All("b",Call("Parts",Id("lb")),body);
        body = All("a",Call("Parts",Id("la")),body);
        foreach (var length in new[] { "ld", "lc", "lb", "la" }) body = All(length,Nat(),body);
        return body;
    }
    private static Formula Listed()
    {
        Formula body = Iff(Call("listed",Id("a"),Id("b")),
            Or(Call("pairIso",Id("a"),Id("b"),Call("baseA"),Call("baseB")),
                Exists("j",Positive(),Call("pairIso",Id("a"),Id("b"),Call("alpha",Id("j")),Call("beta",Id("j"))))));
        return All("la",Nat(),All("lb",Nat(),All("a",Call("Parts",Id("la")),All("b",Call("Parts",Id("lb")),body))));
    }
    private static Formula Size(string a) => Seq(new Formula.Subscript(F.Sum,Id("i")),Sp,Call("val",Call(a,Id("i"))));
    private static Formula Ps(string a, byte k) => Call("ordinary",Call("caterpillar",Id(a)),D(k));
    private static Formula ClaimBody() => All("n",Nat(),Implies(Le(D(1),Id("n")),All("la",Nat(),All("lb",Nat(),
        All("a",Call("Parts",Id("la")),All("b",Call("Parts",Id("lb")),Implies(
            And(Call("admissible",Id("a")),And(Call("admissible",Id("b")),And(Eq(Size("a"),Id("n")),
                And(Eq(Size("b"),Id("n")),And(Ne(Ps("a",2),Ps("b",2)),Eq(Ps("a",3),Ps("b",3))))))),
            Call("listed",Id("a"),Id("b")))))))));
}
