using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class CrupiFicarra52Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/crupificarra2025blockingsemiovals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp maximum in Crupi–Ficarra Open Question 5.2 is q²−q+1 for every finite field of order q≥5.",
        H("The maximum size of a projective blocking set with the r∞-property"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crupificarra52-blocking-set"), DeclarationHandle.Create(Prefix + "BlockingSet"),
                H("Projective blocking set"), StatementSource.FromAuthor(Disp(BlockingSetBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Definition 2.1, arXiv:2507.05037v2, p. 4. “A blocking set of PG(2, q) is a set of points B which meets every line but does not contain any line.”")),
                    Paragraph(Text("The first conjunct requires a point of B on every line. The second says no line is contained in B. Points and line covectors are Mathlib projectivizations of triples, with incidence given by a vanishing dot product.")),
                    Paragraph(Text("Definition 2.1, p. 4, defines minimality separately. “A blocking set B of PG(2, q) (AG(2, q), respectively) is called minimal if no proper subset of B is a blocking set of PG(2, q) (AG(2, q), respectively).”"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crupificarra52-tangent-at"), DeclarationHandle.Create(Prefix + "TangentAt"),
                H("Tangent at a point of the set"), StatementSource.FromAuthor(Disp(TangentAtBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("ArXiv:2507.05037v2, p. 4. “A tangent to K is a line which intersects K in only one point. A secant to K is a line which intersects K in more than one point.”")),
                    Paragraph(Text("The line contains p and any point of B on it equals p. The enclosing RInfinity predicate supplies p ∈ B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crupificarra52-r-infinity"), DeclarationHandle.Create(Prefix + "RInfinity"),
                H("The r∞-property"), StatementSource.FromAuthor(Disp(RInfinityBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Definition 3.1, arXiv:2507.05037v2, p. 5. “Let B be a blocking set in PG(2, q). We say that B has the r∞-property with respect to P ∈ B if there exists through P only one tangent to B, called r∞, and the other lines through P are secants to B. If it is not necessary to specify the point P, we say that B has the r∞-property.”")),
                    Paragraph(Text("The predicate gives p ∈ B, a tangent t and a second point x ≠ p of B on every other line through p. The theorem also requires BlockingSet B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crupificarra52-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The sharp maximum exceeds the proposed threshold"),
                StatementSource.FromAuthor(Disp(ResultBody())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Crupi and Ficarra, Open Question 5.2, arXiv:2507.05037v2, p. 12. “Are there blocking sets with the r∞-property of size k > 3(q−1) in PG(2, q) with q ≥ 5?”")),
                    Paragraph(Text("For any field F with Fintype F and q = Fintype.card F ≥ 5, IsGreatest supplies the attaining set and bounds every qualifying set. The maximum exceeds the threshold by (q−2)².")),
                    Paragraph(Text("In the affine chart z=1, omit the q points (x:x²:1) and keep every other affine point. Include just the vertical direction P=(0:1:0) at infinity. Each vertical line keeps P and q−1 affine points. A nonvertical line y=mx+b keeps at least q−2 points by the root bound for X²−mX−b and omits its point at infinity. The line at infinity keeps just P. These incidences give both blocking conditions and the unique tangent at P in every characteristic.")),
                    Paragraph(Text("For an arbitrary qualifying set, its tangent at p omits q points. Each other line through p omits at least one point, and these q omissions are distinct and off the tangent by uniqueness of the line through two points. The total q²+q+1 points therefore leave room for at most q²−q+1 in the set.")),
                    Paragraph(Text("The witness has a proper blocking subset. Deleting one retained affine point leaves P on the line at infinity and a hit on each of the other lines, which had at least two hits. The paper gives a separate definition for inclusion-minimal blocking sets."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(Formula value, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(value, type)), Comma, Sp, body);
    private static Formula Instance(string name) =>
        Seq(OpenBracket, App(name, FormulaDsl.Id("F")), CloseBracket);
    private static Formula OverField(Formula body) =>
        All(FormulaDsl.Id("F"), Named("Type"), Seq(Instance("Field"), Sp, body));
    private static Formula OverBlockingSet(Formula body) =>
        OverField(All(FormulaDsl.Id("B"), FiniteSets(), body));
    private static Formula Some(Formula binder, Formula body) => Seq(Exists, Sp, binder, Comma, Sp, body);
    private static Formula Member(Formula value, Formula collection) => Seq(value, Sp, InMacro, Sp, collection);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Then(Formula left, Formula right) => Seq(left, Sp, Rightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Nat() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Plane() => Seq(Mathbb, Grp(FormulaDsl.Id("P")), Sp, FormulaDsl.Id("F"), Sp,
        Parenthesized(new Formula.TypeArrow(App("Fin", D(3)), FormulaDsl.Id("F"))));
    private static Formula FiniteSets() => App("Finset", Parenthesized(Plane()));
    private static Formula Card() => new Formula.Apply(Seq(Named("Fintype"), Dot, Named("card")), [FormulaDsl.Id("F")]);

    private static Formula BlockingSetBody()
    {
        Formula hits = All(FormulaDsl.Id("l"), Plane(), Some(Member(FormulaDsl.Id("p"), FormulaDsl.Id("B")), Member(FormulaDsl.Id("p"), FormulaDsl.Id("l"))));
        Formula contained = All(FormulaDsl.Id("p"), Plane(), Then(Member(FormulaDsl.Id("p"), FormulaDsl.Id("l")), Member(FormulaDsl.Id("p"), FormulaDsl.Id("B"))));
        Formula omits = All(FormulaDsl.Id("l"), Plane(), Seq(Neg, Parenthesized(contained)));
        return OverBlockingSet(Equal(App("BlockingSet", FormulaDsl.Id("B")),
            Parenthesized(And(Parenthesized(hits), Parenthesized(omits)))));
    }

    private static Formula TangentAtBody()
    {
        Formula intersectsOnlyAtP = Seq(Forall, Sp, Member(FormulaDsl.Id("x"), FormulaDsl.Id("B")), Comma, Sp,
            Then(Member(FormulaDsl.Id("x"), FormulaDsl.Id("l")), Equal(FormulaDsl.Id("x"), FormulaDsl.Id("p"))));
        Formula body = Equal(App("TangentAt", FormulaDsl.Id("B"), FormulaDsl.Id("p"), FormulaDsl.Id("l")),
            Parenthesized(And(Member(FormulaDsl.Id("p"), FormulaDsl.Id("l")), Parenthesized(intersectsOnlyAtP))));
        return OverBlockingSet(All(FormulaDsl.Id("p"), Plane(), All(FormulaDsl.Id("l"), Plane(), body)));
    }

    private static Formula RInfinityBody()
    {
        Formula secondPoint = Some(Member(FormulaDsl.Id("x"), FormulaDsl.Id("B")),
            And(Member(FormulaDsl.Id("x"), FormulaDsl.Id("l")), Seq(FormulaDsl.Id("x"), Sp, Neq, Sp, FormulaDsl.Id("p"))));
        Formula secants = All(FormulaDsl.Id("l"), Plane(), Then(Member(FormulaDsl.Id("p"), FormulaDsl.Id("l")),
            Then(Seq(FormulaDsl.Id("l"), Sp, Neq, Sp, FormulaDsl.Id("t")), secondPoint)));
        Formula withTangent = Some(Parenthesized(Typed(FormulaDsl.Id("t"), Plane())),
            And(App("TangentAt", FormulaDsl.Id("B"), FormulaDsl.Id("p"), FormulaDsl.Id("t")), Parenthesized(secants)));
        return OverBlockingSet(Equal(App("RInfinity", FormulaDsl.Id("B")),
            Parenthesized(Some(Member(FormulaDsl.Id("p"), FormulaDsl.Id("B")), withTangent))));
    }

    private static Formula ResultBody()
    {
        Formula sizes = Seq(OpenBrace, Typed(FormulaDsl.Id("n"), Nat()), Sp, Mid, Sp,
            Some(Parenthesized(Typed(FormulaDsl.Id("B"), FiniteSets())), And(App("BlockingSet", FormulaDsl.Id("B")),
                And(App("RInfinity", FormulaDsl.Id("B")), Equal(Seq(FormulaDsl.Id("B"), Dot, Named("card")), FormulaDsl.Id("n"))))),
            CloseBrace);
        Formula maxSize = Seq(new Formula.Power(Parenthesized(Card()), D(2)), Sp, Minus, Sp, Card(), Sp, Plus, Sp, D(1));
        Formula threshold = Seq(D(3), Sp, Cdot, Sp, Parenthesized(Seq(Card(), Sp, Minus, Sp, D(1))));
        return OverField(Seq(Instance("Fintype"), Sp,
            Then(Seq(D(5), Sp, Le, Sp, Card()),
                Parenthesized(And(App("IsGreatest", sizes, Parenthesized(maxSize)), Parenthesized(Seq(threshold, Sp, Lt, Sp, maxSize)))))));
    }
}
