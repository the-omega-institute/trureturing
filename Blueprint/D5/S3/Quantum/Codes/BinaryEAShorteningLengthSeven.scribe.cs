using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEAShorteningLengthSevenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven.";
    private static readonly Formula HSpace = V("H");
    private static readonly Formula U = V("U");
    private static readonly Formula i = V("i");
    private static readonly Formula x = V("x");
    private static readonly Formula u = V("u");
    private static readonly Formula h = V("h");
    private static readonly Formula Field = Call("ZMod", D(2));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-site residual Gram argument rules out the remaining rank-two radical case at length seven.",
        H("Length-seven residual obstruction for binary symplectic codes"),
        Blocks(
            Entry("length_seven_no_rank_two_site", "Exclusion of a rank-two radical site at length seven", Seven(),
                "After shortening, a three-site projection excludes radical words of weight at most two and weight-three words supported on mixed radical types. Local symplectic coordinates leave either two triples or three pairs of types. In both profiles the Z projection has kernel equal to the radical and image equal to its annihilator. A weight-two Z vector in the two-triple profile permits three zeros after a radical shift. In the three-pair profile, shifts enforce pair mismatches and parity equations on the four Z-basis lifts. These equations make the symplectic Gram vanish. Lifting through the shortening then makes the original eight-dimensional code isotropic in dimension fourteen."))));

    private static Formula V(string value) => F.Id(value);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n)
    {
        var bits = new Formula.TypeArrow(Fin(n), Field);
        return Paren(Seq(Paren(bits), Sp, Times, Sp, Paren(bits)));
    }
    private static Formula Space(Formula n) => Call("Submodule", Field, Word(n));
    private static Formula Paren(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula v, Formula t, Formula b) =>
        Seq(Forall, Sp, Paren(Seq(v, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Paren(premise), FormulaLogicOperator.Implies, conclusion);
    private static Formula Assumptions(Formula conclusion, params Formula[] premises)
    {
        for (int index = premises.Length - 1; index >= 0; --index)
            conclusion = Implies(premises[index], conclusion);
        return conclusion;
    }
    private static Formula In(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Dim(Formula a) => Call("finrank", Field, a);
    private static Formula Pairing(Formula n, Formula a, Formula b) => Call("spForm", n, a, b);
    private static Formula On(Formula map, Formula space) => Call("domRestrict", map, space);
    private static Formula Surj(Formula map) => Call("Surjective", map);
    private static Formula Not(Formula a) => new Formula.Not(Paren(a));
    private static Formula Zeros(Formula sites, Formula word) => Card(Call("zeroSites", sites, word));
    private static Formula Bound(Formula n, Formula sites, Formula upper, Formula lower, byte k) =>
        All(x, Word(n), Assumptions(Le(Zeros(sites, x), D(k)), In(x, upper), Not(In(x, lower))));
    private static Formula Orth(Formula n) => All(h, Word(n), Implies(In(h, HSpace),
        All(u, Word(n), Implies(In(u, U), Equal(Pairing(n, h, u), D(0))))));
    private static Formula FiniteSpaces(Formula n, Formula body) =>
        All(HSpace, Space(n), All(U, Space(n), body));
    private static Formula Standard(Formula n, Formula body) => FiniteSpaces(n,
        Assumptions(body, Le(HSpace, U), Equal(Dim(HSpace), D(4)), Equal(Dim(U), D(8)),
            Orth(n), Bound(n, V("univ"), U, HSpace, 3)));
    private static Formula Seven() => Standard(D(7), All(i, Fin(D(7)),
        Assumptions(V("False"), Surj(On(Call("site", i), HSpace)))));

    private static DocumentBlock Entry(string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create("binary-ea-shortening-length-seven-" + name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);
}
