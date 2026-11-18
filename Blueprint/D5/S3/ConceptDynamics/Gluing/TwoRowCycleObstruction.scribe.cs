using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class TwoRowCycleObstructionDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] binders) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);
    private static Formula Some(Formula body, params Formula.BoundVariable[] binders) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. binders], body);
    private static Formula Fn(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var k = clauses.Length - 2; k >= 0; --k)
            result = new Formula.Logic(clauses[k], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Member(Formula item, Formula set) =>
        Seq(item, Sp, InMacro, Sp, set);
    private static Formula Not(Formula body) => Seq(Neg, Open, body, Close);
    private static Formula C(Formula index) => Call("c", index);
    private static Formula S(Formula index) => Call("S", index);
    private static Formula R(Formula index) => Call("R", index);
    private static Formula Rotate(Formula index) => Call("finRotate", I("n"), index);

    private static Formula Statement()
    {
        var e = I("e");
        var f = I("f");
        var i = I("i");
        var j = I("j");
        var fin = Call("Fin", I("n"));
        var edgeCover = All(Some(
            And(Member(C(i), S(e)), Member(C(Rotate(i)), S(e))), B("e", I("E"))),
            B("i", fin));
        var chord = All(Imp(Not(Equal(i, j)),
            Imp(Member(C(i), S(e)), Imp(Member(C(j), S(e)),
                Or(Equal(Rotate(i), j), Equal(Rotate(j), i))))),
            B("e", I("E")), B("i", fin), B("j", fin));
        var pair = Seq(OpenBrace, I("a"), Comma, Sp, I("b"), CloseBrace);
        var local = All(Some(Equal(R(e), pair),
            B("a", Fn(S(e), I("Bool"))), B("b", Fn(S(e), I("Bool")))),
            B("e", I("E")));
        var overlap = All(Equal(
            Call("leftProjection", I("S"), e, f, R(e)),
            Call("rightProjection", I("S"), e, f, R(f))),
            B("e", I("E")), B("f", I("E")));
        var emptyJoin = Not(Some(All(Member(
            Call("restrict", I("g"), S(e)), R(e)), B("e", I("E"))),
            B("g", Fn(I("V"), I("Bool")))));
        var relationFamily = Seq(Pi, Sp, e, Colon, I("E"), Comma, Sp,
            Call("Set", Fn(S(e), I("Bool"))));
        return Disp(All(
            All(Imp(Seq(D(4), Sp, Leq, Sp, I("n")),
                    All(Imp(Call("Injective", I("c")),
                        Imp(edgeCover, Imp(chord,
                            Some(And(local, overlap, emptyJoin), B("R", relationFamily))))),
                        B("c", Fn(fin, I("V"))))),
                    B("S", Fn(I("E"), Call("Set", I("V")))), B("n", I("Nat"))),
            B("u", I("Universe")), B("v", I("Universe")),
            B("E", new Formula.Subscript(I("Type"), I("u"))),
            B("V", new Formula.Subscript(I("Type"), I("v")))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every induced cycle of length at least four supports one or two Boolean rows per "
            + "scope with equal complete overlap projections and empty natural join.",
        H("Two Row Cycle Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-row-cycle-full-overlap-obstruction"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction."
                + "two_row_cycle_obstruction"),
            H("Full overlap consistency without a global assignment"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/ConceptDynamics/beeri1983acyclic")),
            Blocks(
                Paragraph(Text(
                    "The universes u and v are independent. E is an arbitrary scope index type "
                        + "and V is an arbitrary variable type; either carrier may be infinite. "
                        + "S assigns a set of variables to each scope. The injection c lists n "
                        + "distinct cycle vertices, with n at least four. Every consecutive cycle "
                        + "pair lies in a scope. Within any scope, two distinct cycle indices "
                        + "must be consecutive in one of the two orientations.")),
                Paragraph(Text(
                    "A scope A in a function type denotes its subtype of variables. The local "
                        + "clause states explicitly that R(e)={r0,r1} for two functions on S(e). "
                        + "These functions may coincide when the scope contains no cycle vertex; "
                        + "each relation therefore has one or two rows. For fixed e and f, both "
                        + "projection images use the same carrier (S(e) intersect S(f)) to Bool. "
                        + "leftProjection(S,e,f,R(e)) is the image of R(e) under r mapping to "
                        + "(x mapping to r(x)), where x belongs to that complete intersection "
                        + "and is viewed in S(e). rightProjection uses the same x viewed in S(f). "
                        + "restrict(g,A) is x mapping to g(x) on A. One family R satisfies all "
                        + "these clauses simultaneously, and no ambient assignment g satisfies "
                        + "all its local relations.")),
                Paragraph(Text(
                    "Write z=c(0) and l=c(n-1). For each scope A and variable x let p_A(x) "
                        + "be the Boolean indicator of z in A and x=l. For b in Bool define "
                        + "row(A,b)(x)=b xor p_A(x) when x lies in the range of c, and false "
                        + "otherwise. R(A) is the range of this Boolean indexed constructor, "
                        + "equivalently {row(A,false),row(A,true)}. Every off-cycle coordinate "
                        + "is false, regardless of the size of A or V.")),
                Paragraph(Text(
                    "If A contains both z and l, chordlessness forces its cycle support into "
                        + "{z,l}: an additional cycle vertex would have to be adjacent to both "
                        + "endpoints of this edge, which is impossible for n at least four. "
                        + "Consequently p_A(c(i)) xor p_B(c(i)) is constant as i ranges over "
                        + "the shared cycle support. When z belongs to exactly one scope, two "
                        + "shared vertices with different potentials would force z into the "
                        + "other scope as well.")),
                Paragraph(Text(
                    "To match row(A,b) on B, choose a shared cycle anchor j when one exists "
                        + "and put d=b xor p_A(c(j)) xor p_B(c(j)). The constant difference "
                        + "law gives row(B,d)=row(A,b) on every shared cycle coordinate. With "
                        + "no shared cycle vertex choose d=false. On all other coordinates in "
                        + "the complete intersection both rows are false. Phase alignment thus "
                        + "preserves the entire intersection. Applying this construction in "
                        + "each ordered direction proves equality of both full projection images.")),
                Paragraph(Text(
                    "A global satisfying assignment would have equal values along the "
                        + "successor path from c(0) to c(n-1). The closing edge lies in a scope "
                        + "containing both endpoints, where their values are opposite. This is "
                        + "a contradiction. The edge charge is zero along the successor path "
                        + "and one at the closing edge, so its total is odd for every n, "
                        + "including even n.")),
                Paragraph(Text(
                    "Empty, duplicate and contained scopes, coordinates outside the cycle, "
                        + "and variables outside the union of all scopes remain allowed. No "
                        + "finiteness, nonemptiness or decidable equality assumption is imposed "
                        + "on E or V. The classical acyclic database scheme theorem supplies "
                        + "background for pairwise projection consistency in finite schemes. "
                        + "The explicit Boolean construction here gives at most two rows per "
                        + "scope and an empty join over arbitrary carriers. This precise "
                        + "statement is not attributed verbatim to that paper, and no claim "
                        + "of originality or full acyclicity classification is made."))),
            DescribeRole.Theorem))));
}
