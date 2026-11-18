using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookClassCandidateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookClassCandidate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The registered weighted-root sum is evaluated on a finite disjoint family; its identification with the full native rook class remains open.",
        H("The exact weighted-root candidate and its fiber assembly"), Blocks(
            Definition("sourcePadding", "Ordered source padding",
                "Apply the existing lOperator to the arbitrary normalized input board, retaining its ordered top-down nonempty level totals and its explicit empty-board extension. Prepend zeros to the requested common length. The padding theorem derives the length bound from literal source cells and does not assume rook-number preservation."),
            Definition("seedRoots", "The registered root multiset",
                "At zero-based position i take mi minus the corresponding entry of sourcePadding, in the integers. The common-padding theorem proves that every registered length has exactly that many entries and the first root is zero."),
            Definition("weight", "Fully evaluated fiber weights",
                "Return zero if any target entry is nonpositive. Otherwise use the existing count recurrence with r=m-1, the reversed target list and its first bottom-up entry U, defaulting to zero for the empty list. The recurrence sums over v from zero through U, uses the guarded coefficient of the q-Pascal Gaussian polynomial in transition, and has empty-list value one. This is the exact evaluated weight of the registration. It is an ordinary count of shapes, not the file-placement weight in the paper's separate weighted question."),
            Definition("Q", "The fixed candidate",
                "Sum weight(m,board(m,a)) over the finite subtype of distinct admissible root indices of seedRoots(m,N,B). A normalized representative is used exactly once. This definition enumerates root-multiset sequences and evaluates the finite Gaussian recurrence; it does not enumerate the original class of Ferrers boards. The first position, nonnegativity, Ferrers order and conditional floor test are all retained in indices."),
            Definition("K", "The native class cardinality",
                "K is Nat.card of the class defined by equality of every literal rook-subset count. The separate rookClass_finite theorem proves this carrier finite using an explicit injection into the powerset of the area-square. Thus the infinite-carrier convention of Nat.card is not used to assert class finiteness."),
            Definition("UniversalFormula", "The unproved universal target",
                "UniversalFormula asserts K(m,B)=Q(m,N,B) for every positive m, every normalized positive-column input including the empty board, and every N at least area(B)+1. This declaration defines a proposition. No proof of it or its negation is provided here. In particular, the fiber-assembly theorem below does not identify its RootFamily with the native rook class."),
            Definition("RootFamily", "The actual root-selected source family",
                "A normalized source shape belongs precisely when its actual lOperator value equals board(m,a) for some index a of the fixed seed z. The quantifier ranges over the same arbitrary-width, arbitrary-height positive-column shapes as the native class. It imposes no singleton restriction on these original source shapes."),
            Definition("rootFiberEquiv", "A disjoint union on the same actual shapes",
                "The dependent sum over root indices of the actual lOperator fibers maps to RootFamily by forgetting the index. Injectivity of root reconstruction forces equal indices whenever the underlying source shape agrees. Surjectivity uses the very witness of family membership. This is a bijection of the same shapes, with no replacement by independently achievable marginal counts."),
            Theorem("rootFamily_count", "Finite family and evaluated ordinary cardinality", FamilyCount(),
                "Every lOperator fiber is finite: the existing operatorFiberEquiv and the publicly reusable original sourceShapeEquiv transport it to ShapeFiber, then normalizedPaddingEquiv transports it to the existing finite NativeFiber. Invalid positive-target data give an empty fiber. The finite index therefore gives a finite dependent sum and a finite RootFamily. Nat.card_sigma and the direct application of BarreseSourceNormalization.lOperator_count evaluate every fiber with the exact guarded recurrence. In the displayed formula, sumWeights(m,z) denotes the sum over a in indices(m,z) of weight(m,board(m,a)); board is read as its underlying positive list. Applying this theorem to z=seedRoots(m,N,B) gives cardinality Q for RootFamily, while the native-class identification remains open."),
            Theorem("candidate_padding", "Every registered common length", Padding(),
                "For every positive m, arbitrary normalized B and N at least area(B)+1, lOperator(m,B) has length below N, sourcePadding has length N and a zero head, and seedRoots is zero at its first coordinate. To bound the number of levels, inspect the last nonempty level. Its positive total supplies an actual occupied cell in some column. That column's height is at most the area and exceeds m times the level index, so the number of nonempty levels is at most the area. This includes the empty board without an extra premise."),
            Paragraph(Text("The first unresolved mathematical interface is the level-total factorization for the native rookCount on every arbitrary input: the sum of r(k,m,B) times the m-step falling factorial of length N-k must equal the product over i of X minus seedRoots(m,N,B,i). The source is Theorem 26 of arXiv:1508.05944v1; its proof uses the arbitrary-board reduction through Lemmas 3 and 5 and singleton factorization. Those literature statements have not been imported as assumptions. A complete result still needs this native bridge or an equivalent bijection, the complete singleton image and inverse, area preservation of the actual l-operator, and all-length class identification. The root-selected family count and finite probes do not prove any of those missing interfaces. The exact full target remains issue #31465."))
        ), []));
    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rookclasscandidate-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rookclasscandidate-" + declaration.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula I(string name) => F.Id(name);
    private static Formula Nat() => I("Nat");
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, Seq(Open, y, Close));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula FamilyCount() => All("m", Nat(), Imp(Lt(D(0), I("m")), All("n", Nat(),
        All("z", new Formula.TypeArrow(Call("Fin", I("n")), new Formula.Integers()),
            And(Call("Finite", Call("RootFamily", I("m"), I("z"))),
                Eq(Call("int", Call("card", Call("RootFamily", I("m"), I("z")))), Call("sumWeights", I("m"), I("z")))))));
    private static Formula Padding()
    {
        Formula m = I("m"), n = I("n"), b = I("b"), i = I("i"), c = Call("lOperator", m, b), p = Call("sourcePadding", m, n, b);
        return All("m", Nat(), Imp(Lt(D(0), m), All("b", I("PositiveColumns"), All("n", Nat(),
            Imp(new Formula.Relation(new Formula.Binary(Call("area", b), FormulaBinaryOperator.Add, D(1)), FormulaRelationOperator.LessThanOrEqual, n),
                And(Lt(Call("length", c), n), And(Eq(Call("length", p), n),
                    And(Eq(Call("head", p), Call("some", D(0))), All("i", Call("Fin", n),
                        Imp(Eq(Call("val", i), D(0)), Eq(Call("seedRoots", m, n, b, i), D(0)))))))))));
    }
}
