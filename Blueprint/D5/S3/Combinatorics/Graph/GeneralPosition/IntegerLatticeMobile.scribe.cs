using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class IntegerLatticeMobileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/klavzaretal2026mobileproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive dimensional integer lattice has attained mobile general position number two to the power two to the power dimension minus one.",
        H("The attained mobile general position number of the integer lattice"),
        Blocks(
            Paragraph(Text("For a natural dimension k, the vertices are all functions Fin k -> Int. The graph IntegerLatticeMotion.lattice k joins two vertices exactly when one coordinate changes by +1 or -1 and every other coordinate agrees. It is connected, and its graph distance is the sum of the absolute coordinate differences. CylinderSevenTen.IsGeneralPosition excludes every ordered triple of pairwise distinct occupied vertices whose middle vertex lies on a shortest path between the endpoints.")),
            Paragraph(Text("CylinderSevenTen.LegalMove G A B means that there are u in A and v outside A with G.Adj u v, B = insert v (A.erase u), and B in general position. Thus one occupied vertex moves along one actual edge into a vacant vertex and all other occupied vertices stay fixed. The occupied sets are finite, while the graph and the time index are unbounded.")),
            Node("mobility", "One common covering trajectory", "IsMobile", DescribeRole.Definition,
                All("k", Nat(), All("S", Config(),
                    Eq(Call("IsMobile", X("S")), Par(MobileBody())))),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1 defines a mobile general position set by a sequence of legal moves starting at the set and visiting every graph vertex. Here the infinite lattice uses one sequence c indexed by all natural times. The same c starts at S, makes a legal move at every time, remains in general position at every time, and contains each lattice vertex at some finite time. Initial general position is explicit. No constant-cardinality premise is added."),
            Node("result", "The exact bound is attained in every positive dimension", "result", DescribeRole.Theorem,
                All("k", Nat(), Imp(Le(D(1), X("k")), And(
                    Par(All("S", Config(), Imp(Call("IsMobile", X("S")), Le(Card(), Bound())))),
                    Par(Ex("S", Config(), And(Call("IsMobile", X("S")), Eq(Card(), Bound()))))))),
                AssessedProvenance.FromRepo(Source),
                "Section 5, second bullet, asks whether the known static value 2^(2^(k-1)) is also the mobile value in higher dimensional infinite grids. The theorem gives both the upper bound for every finite mobile S and an actual finite mobile set attaining it, for every natural k at least one, including all k at least three. The upper bound uses only initial general position: graph geodesic betweenness equals coordinate betweenness, so IntegerLatticeStatic.card_le applies, including to the empty set. IntegerLatticeStatic.exists_attaining supplies a nonempty coordinate general-position set S of the exact size. IntegerLatticeFiniteMotion.scaled_finset_mobile supplies one common covering trajectory from the fourfold image of S and proves that this image has the same cardinality. Its additional derived cardinality invariant is discarded when proving IsMobile. The initial attaining set is the fourfold image; no motion from the unscaled S to that image is asserted. There is no restriction to a finite box or to a bounded traversal duration, and no assumed optimum or independent trajectory for each target vertex.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klavzar-et-al-2025-mobile-general-position-integer-lattices"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            role, openProblemResolutionClaim: resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name)))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Vertex() => new Formula.TypeArrow(Call("Fin", X("k")), Int());
    private static Formula Config() => Call("Finset", Par(Vertex()));
    private static Formula Graph() => Qualified("IntegerLatticeMotion", "lattice", X("k"));
    private static Formula At(Formula t) => new Formula.Apply(X("c"), [t]);
    private static Formula GP(Formula s) => Qualified("CylinderSevenTen", "IsGeneralPosition", Graph(), s);
    private static Formula Card() => Qualified("Finset", "card", X("S"));
    private static Formula Bound() => new Formula.Power(D(2), new Formula.Power(D(2),
        new Formula.Binary(X("k"), FormulaBinaryOperator.Subtract, D(1))));
    private static Formula MobileBody() => And(GP(X("S")),
        Ex("c", new Formula.TypeArrow(Nat(), Config()), And(Eq(At(D(0)), X("S")),
            And(Par(All("t", Nat(), Qualified("CylinderSevenTen", "LegalMove", Graph(),
                    At(X("t")), At(Add(X("t"), D(1)))))),
                And(Par(All("t", Nat(), GP(At(X("t"))))),
                    Par(All("x", Vertex(), Ex("t", Nat(), Member(X("x"), At(X("t")))))))))));
}
