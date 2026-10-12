using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class WindowSeamCodesDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.";

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula NotMember(Formula left, Formula right) =>
        new Formula.Not(Member(left, right));

    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);

    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula Card(Formula value) => Call("card", value);

    private static Formula Unary(Formula clauses, Formula index) => Call("unary", clauses, index);

    private static Formula Extra(Formula clauses) => Call("extra", clauses);

    private static Formula Pair(Formula clauses, Formula index) => Call("pair", clauses, index);

    private static Formula ClauseLaw(Formula clauses, Formula dimension, Formula label, Formula word)
    {
        var i = F.Id("i");
        return And(
            All("i", Call("Fin", dimension),
                Imp(Equal(Unary(clauses, i), label), NotMember(i, word))),
            Imp(Equal(Extra(clauses), label), NotMember(D(0), word)),
            All("i", Call("Fin", dimension),
                Imp(And(Lt(D(0), Call("val", i)), Equal(Pair(clauses, i), label)),
                    Or(NotMember(i, word), NotMember(Call("prev", i), word)))));
    }

    private static Formula Selected(Formula clauses, Formula dimension, Formula labelType, Formula code)
    {
        var label = F.Id("L"); var i = F.Id("i");
        var regular = All("L", labelType,
            Member(Apply(code, label), Call("codeList", clauses, label)));
        var two = Call("castClauses", D(2), clauses);
        var ctwo = Call("castCodes", D(2), code);
        var exceptional = And(Equal(dimension, D(2)), Equal(Card(labelType), D(4)),
            Call("Injective", Call("fourOwners", two)),
            All("i", Call("Fin", D(4)),
                Equal(Apply(ctwo, Call("fourOwner", two, i)), Call("fourWords", i))),
            All("i", Call("Fin", D(2)), NotMember(i, Apply(ctwo, Unary(two, i)))),
            NotMember(D(0), Apply(ctwo, Extra(two))),
            Member(D(0), Apply(ctwo, Pair(two, D(1)))),
            Member(D(1), Apply(ctwo, Pair(two, D(1)))));
        return Or(regular, exceptional);
    }

    private static Formula VertexFacts(Formula width, Formula dimension, Formula index)
    {
        var phase = Call("ZMod", Add(width, D(2))); var j = F.Id("j");
        var r = Add(Call("val", index), D(1));
        var missed = Call("cast", Call("val", Call("missedVertex", width, dimension, index)), phase);
        var seam = Call("cast", Call("val", Call("seamVertex", width, dimension, index)), phase);
        var window = Call("sourceWindow", width, r);
        return And(All("j", phase, Iff(Member(j, window), Ne(j, missed))),
            Member(Call("cast", Add(width, D(1)), phase), window),
            Equal(Call("cast", Multiply(r, width), phase), seam),
            Equal(Call("cast", Add(Multiply(Call("val", index), width), width), phase), seam));
    }

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var y = F.Id("Y");
        var d = F.Id("d"); var m = F.Id("m"); var clauses = F.Id("C");
        var label = F.Id("L"); var word = F.Id("w"); var s = F.Id("S");
        var i = F.Id("i"); var code = F.Id("c"); var table = F.Id("table");
        var clauseType = Call("Clauses", d, y);
        var regular = Or(Le(D(3), d), Or(Le(Card(Call("owners", clauses)), D(3)), Le(Card(y), D(3))));
        var union = All("Y", F.Id("FiniteType"), All("d", nat, All("C", clauseType,
            Imp(And(Le(D(2), d), Le(Card(y), new Formula.Power(D(2), d)), regular),
                All("S", Call("Finset", y), Le(Card(s), Card(Call("listUnion", clauses, s))))))));
        var semantics = All("Y", F.Id("Type"), All("d", nat, All("C", clauseType,
            Imp(Lt(D(0), d), All("L", y, All("w", Call("Word", d),
                Iff(Member(word, Call("codeList", clauses, label)),
                    ClauseLaw(clauses, d, label, word))))))));
        var vertices = All("m", nat, All("d", nat,
            Imp(Le(Multiply(D(2), d), Add(m, D(1))),
                All("i", Call("Fin", d), VertexFacts(m, d, i)))));
        var sourceLabels = Call("Label", table);
        var sourceClauses = Call("sourceClauses", table, d);
        var unary = All("i", Call("Fin", d),
            NotMember(i, Apply(code, Unary(sourceClauses, i))));
        var geometry = And(
            All("i", Call("Fin", d), All("j", Call("ZMod", Add(m, D(2))),
                Iff(Member(F.Id("j"), Call("sourceWindow", m, Add(Call("val", i), D(1)))),
                    Ne(F.Id("j"), Call("cast", Call("val", Call("missedVertex", m, d, i)),
                        Call("ZMod", Add(m, D(2)))))))),
            All("i", Call("Fin", d), Member(Call("cast", Add(m, D(1)), Call("ZMod", Add(m, D(2)))),
                Call("sourceWindow", m, Add(Call("val", i), D(1))))),
            All("i", Call("Fin", d), Equal(Call("cast", Multiply(Add(Call("val", i), D(1)), m),
                Call("ZMod", Add(m, D(2)))), Call("cast", Call("val", Call("seamVertex", m, d, i)),
                    Call("ZMod", Add(m, D(2)))))),
            All("i", Call("Fin", d), Equal(Call("cast", Add(Multiply(Call("val", i), m), m),
                Call("ZMod", Add(m, D(2)))), Call("cast", Call("val", Call("seamVertex", m, d, i)),
                    Call("ZMod", Add(m, D(2)))))));
        var selection = All("Y", F.Id("Type"), All("m", nat,
            All("table", Arrow(Call("Fin", Add(m, D(1))), y),
                Imp(And(Call("Odd", m), Le(D(3), Card(Call("labels", table)))),
                    All("d", nat, Imp(Equal(d, Call("clog", D(2), Card(Call("labels", table)))),
                        And(Le(Multiply(D(2), d), Add(m, D(1))), Le(D(2), d),
                            Exists("c", Arrow(sourceLabels, Call("Word", d)),
                                And(Call("Injective", code), Call("Injective", Call("bitCodes", code)),
                                    Selected(sourceClauses, d, sourceLabels, code),
                                    unary, NotMember(D(0), Apply(code, Extra(sourceClauses))), geometry)))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Binary label codes respect missed vertices and adjacent seam clauses.",
            H("Simultaneous codes for a full positive window"),
            Blocks(
                Paragraph(Text(
                    "A word in Word(d) is a finite set of occupied coordinates in Fin(d); "
                    + "wordBits(w)(i) is the Boolean decision of membership, so membership "
                    + "means bit one. bitCodes(c) maps L to wordBits(c(L)). Fin coordinates "
                    + "are zero based, so source "
                    + "coordinate r is i+1. Clauses(d,Y) has unary(i), extra, and pair(i) "
                    + "owners, with pair(0) unused. A label may own any number of these "
                    + "occurrences. forbidden(C,w) is the union of unary owners at occupied "
                    + "coordinates, extra when coordinate zero is occupied, and pair owners "
                    + "at occupied adjacent coordinates. codeList(C,L) consists of all words "
                    + "not forbidden for L. owners(C) is the image of all displayed occurrences. "
                    + "All implicit label types have decidable equality; FiniteType additionally "
                    + "has a finite enumeration. Proof arguments for positive dimensions and "
                    + "valid indices are suppressed in displayed function applications.")),
                Describe.Lean(DescribeId.Create("list-union-inequalities"),
                    DeclarationHandle.Create(Owner + "list_union_inequalities"),
                    H("Low-weight words prove every subfamily inequality"),
                    StatementSource.FromAuthor(Disp(union)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "listUnion(C,S) is the union of codeList(C,L) over L in S. A label "
                        + "outside owners(C) contributes the entire cube of size 2^d. Otherwise "
                        + "the subfamily has at most 2d labels. Every list contains zero. "
                        + "For two labels the zero word and the units outside coordinate zero "
                        + "give at least d words. For three or more labels every unit lies in "
                        + "the union, since a unit violates at most two owners. For at least "
                        + "d+2 labels in dimension at least three, all words of weight two "
                        + "also lie in the union: they violate at most three unary occurrences "
                        + "and one adjacent pair. Distinct occupied adjacent pairs would "
                        + "require at least three coordinates. The zero, unit and weight-two "
                        + "layers have total size 1+d+choose(d,2), at least 2d for d>=3. "
                        + "The counts use finite powerset layers. The two-dimensional "
                        + "four-owner case is excluded from this regular inequality."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("code-list-semantics"),
                    DeclarationHandle.Create(Owner + "mem_codeList_iff"),
                    H("List membership is exactly the three source restrictions"),
                    StatementSource.FromAuthor(Disp(semantics)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The unary owner forces its own coordinate to zero. The extra owner "
                        + "forces coordinate zero to zero. Each pair owner at i>0 forces one "
                        + "of i and prev(i) to zero, where prev(i) has value val(i)-1. "
                        + "Repeated labels collect all these conditions."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("source-window-vertices"),
                    DeclarationHandle.Create(Owner + "source_window_vertices"),
                    H("The clauses use the actual ordered window vertices"),
                    StatementSource.FromAuthor(Disp(vertices)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "sourceWindow(m,r) is the image of r*m+h, for 0<=h<=m, in ZMod(m+2). "
                        + "missedVertex(m,d,i) has value m+1-2*(i+1), and seamVertex has value "
                        + "m+2-2*(i+1). Translation of the m+1 consecutive offsets misses "
                        + "exactly the vertex immediately before its start. The period "
                        + "identity m=-2 identifies that vertex with missedVertex. The donor "
                        + "m+1 is present in every window and outside the child table. "
                        + "For r>=2 the preceding window ends at (r-1)*m+m=r*m, the very "
                        + "start of this window. Rotation by the known already-issued offset "
                        + "a*m turns the absolute window at a+r into this same sourceWindow."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("actual-table-codes"),
                    DeclarationHandle.Create(Owner + "actual_table_codes"),
                    H("Every actual label receives a distinct lawful or exceptional word"),
                    StatementSource.FromAuthor(Disp(selection)), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "table is the original label map on every vertex 0 through m of "
                            + "the rotated full positive child. labels(table) is its full image, "
                            + "and Label(table) is the type of members of that image, including "
                            + "unrestricted labels. sourceClauses(table,d) assigns the unary "
                            + "owner table(missedVertex(i)), extra owner table(m), and pair "
                            + "owner table(seamVertex(i)). No code or matching is assumed. "
                            + "clog(2,n) is the least natural d with n<=2^d. The table has at "
                            + "most m+1 labels; odd m and 2*q<=2^q for q>=1 imply 2*d<=m+1, "
                            + "while n>=3 implies d>=2. The finite Hall theorem supplies the "
                            + "injective choice from the proved list inequalities.")),
                        Paragraph(Text(
                            "The displayed Selected condition expands as the disjunction "
                            + "of regular list membership and the explicit second branch. "
                            + "castClauses and castCodes transport along d=2. fourOwners(C) "
                            + "enumerates unary(0), extra, unary(1), pair(1); fourOwner(C,i) "
                            + "is its value. These are exactly LA=table(m-1), LB=table(m), "
                            + "LC=table(m-3), LD=table(m-2). fourWords enumerates the occupied "
                            + "sets empty, {1}, {0}, {0,1}, hence the source words 00,01,10,11. "
                            + "In the second branch there are exactly four labels and these "
                            + "four owners are distinct. All unary and first-bit restrictions "
                            + "hold, while LD has both adjacent bits one. That branch does "
                            + "not satisfy the regular pair clause.")),
                        Paragraph(Text(
                            "This result selects simultaneous codes and identifies their "
                            + "source vertices. Even rotated charge rows, their compensation "
                            + "at the donor, the native endpoint inverse, the exceptional "
                            + "physical seam and a full INITIAL decoder require further "
                            + "integration. No price or GLOBAL controller conclusion follows "
                            + "from code selection alone."))), DescribeRole.Theorem))));
    }
}
