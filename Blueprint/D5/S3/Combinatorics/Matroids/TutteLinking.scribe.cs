using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class TutteLinkingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite matroid has a minor on the two terminal sets that realizes their minimum separating-cut connectivity.",
        H("Tutte linking for finite native matroids"),
        Blocks(Describe.Lean(
            DescribeId.Create("tutte-linking"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/TutteLinking.tutte_linking"),
            H("An actual terminal minor attaining the cut minimum"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/bruhnwollan2011finiteconnectivity")),
            Blocks(
                Paragraph(Text("Let E : Type u be any finite type in any universe u, and let M be any native Matroid E. Let S and T be disjoint subsets of M.E. Define rk M X = ENat.toNat (M.eRk X), cut M X = rk M X + rk M (M.E minus X) - rk M M.E, and kappa M S T to be the natural-number infimum of all cut M X with S contained in X and X contained in M.E minus T. The complement is always relative to the ground of the matroid appearing in that cut.")),
                Paragraph(Text("There exists a set C contained in M.E minus (S union T). Put D = (M.E minus (S union T)) minus C and N = (M / C) minus D, using native matroid contraction and deletion. Then N.E equals S union T, and rk N S + rk N T - rk N (S union T) equals kappa M S T. Thus C and D partition exactly the nonterminal ground, and the conclusion supplies an actual minor. On this terminal ground the sole feasible separating cut is S, so its terminal rank defect is also its minimum separating-cut connectivity.")),
                Paragraph(Text("Finiteness of E makes every native rank used here finite; ENat.toNat therefore preserves rank values and addition. Rank subadditivity makes both displayed rank defects nonnegative before natural subtraction. Empty terminals, empty ground, loops, coloops and rank zero are included. There is no representability, positive-connectivity or nonempty-terminal assumption, and no optimum, certificate or minor is supplied as a premise.")),
                Paragraph(Text("For the construction, put R = M.E minus (S union T), A = (M / S) minus T and B = (M / T) minus S. Both matroids have ground R. Finite matroid intersection supplies a single common independent set I and an attaining rank cut X. Its universal upper bound makes I maximum in cardinality. If an element of M.E lay outside the closure of S union T union I, adjoining it to I would remain independent in both A and B, contradicting that upper bound. Consequently S union T union I spans M.")),
                Paragraph(Text("Take C = I. Independence in M / S and M / T implies rk M (S union I) = rk M S + I.ncard and rk M (T union I) = rk M T + I.ncard. Independence in M gives rk M I = I.ncard. The contraction rank identity and deletion of only nonterminals then give rk N S = rk M S, rk N T = rk M T and rk N (S union T) + I.ncard = rk M M.E. These identities express the terminal rank defect in terms of the same intersection certificate.")),
                Paragraph(Text("The attaining intersection cut X yields the feasible original cut S union X; its complement is (R minus X) union T. The two contraction rank identities show that its connectivity equals the terminal rank defect. For every other feasible original cut Y, apply the common-independent upper bound to Y minus S. Its complementary side in R, together with T, is M.E minus Y. The same rank identities show that the terminal rank defect is at most cut M Y. The feasible cut family is nonempty, its minimum is attained by S union X, and the infimum is exactly the asserted minor value.")),
                Paragraph(Text("Bruhn and Wollan, arXiv:1101.5621v1, pages 1–2, define the finite rank connectivity and the minimum over separating cuts and state this classical partition theorem as Theorem 1, attributed to Tutte. The finite intersection theorem is reused from FiniteIntersection.finite_matroid_intersection; the contraction rank identity is FiniteIntersection.contract_eRk_add. The construction applies to all finite native matroids, including nonrepresentable ones."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var terminals = Union(V("S"), V("T"));
        var outside = Diff(Ground("M"), terminals);
        var minor = A(Q("Matroid", "delete"), A(Q("Matroid", "contract"), V("M"), V("C")), V("D"));
        var defect = Seq(Rank("N", V("S")), Sp, Plus, Sp, Rank("N", V("T")), Sp, Minus, Sp,
            Rank("N", Parenthesized(terminals)));
        Formula result = And(Equal(Ground("N"), terminals),
            Equal(defect, A(Q("TutteLinking", "kappa"), V("M"), V("S"), V("T"))));
        result = Let("N", A(V("Matroid"), V("E")), minor, result);
        result = Let("D", SetType, Diff(outside, V("C")), result);
        result = Some("C", SetType, And(Subset(V("C"), outside), result));
        result = Imp(A(V("Disjoint"), V("S"), V("T")), result);
        result = Imp(Subset(V("T"), Ground("M")), result);
        result = Imp(Subset(V("S"), Ground("M")), result);
        result = All("T", SetType, result);
        result = All("S", SetType, result);
        result = All("M", A(V("Matroid"), V("E")), result);
        result = Seq(OpenBracket, A(V("Finite"), V("E")), CloseBracket, Sp, result);
        return All("E", new Formula.Subscript(V("Type"), V("u")), result);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula A(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula SetType => A(V("Set"), V("E"));
    private static Formula Ground(string matroid) => A(Q("Matroid", "E"), V(matroid));
    private static Formula Rank(string matroid, Formula set) => A(Q("TutteLinking", "rk"), V(matroid), set);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Union(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cup, Sp, Parenthesized(b));
    private static Formula Diff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Setminus, Sp, Parenthesized(b));
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(V("let"), Sp, V(name), Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi, Sp, body);
}
