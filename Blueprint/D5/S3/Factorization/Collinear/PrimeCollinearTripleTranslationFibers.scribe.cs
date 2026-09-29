using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Collinear;

internal sealed class PrimeCollinearTripleTranslationFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation fibers of admissible collinear triples over a prime residue field.",
        H("Prime Collinear Triple Translation Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-collinear-triple-translation-fibers"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Collinear/PrimeCollinearTripleTranslationFibers.translation_orbit_iff"),
                H("Slope and translated abscissae classify translation orbits"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every admissible triple over a prime residue field is the graph of a unique "
                    + "nonzero-slope affine line on a three-element set of first coordinates. "
                    + "Translation by (h,k) sends the slope a, intercept b, and abscissa set X "
                    + "to (a,b+k-ah,h+X). Thus a translation preserves the slope and shifts X "
                    + "by h. Conversely, equal slopes and X'=h+X determine the vertical shift "
                    + "k=b'-b+ah, so the intercepts add no orbit obstruction. This includes "
                    + "the empty family at p=2 and the nonempty case p=3."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Statement()
    {
        var p = F.Id("p");
        var hp = F.Id("hp");
        var s = F.Id("s");
        var t = F.Id("t");
        var ps = Call("parametersOfTriple", p, hp, s);
        var pt = Call("parametersOfTriple", p, hp, t);
        var slopeS = Call("val", Call("fst", Call("fst", ps)));
        var slopeT = Call("val", Call("fst", Call("fst", pt)));
        var xs = Call("val", Call("snd", ps));
        var xt = Call("val", Call("snd", pt));
        var orbit = Seq(s, Sp, InMacro, Sp, Call("orbit", Call("Point", p), t));
        var criterion = And(slopeS, slopeT, xs, xt);
        return Universal("p", Call("Nat"),
            Universal("hp", Call("Prime", p),
                Universal("s", Call("Triple", p),
                    Universal("t", Call("Triple", p),
                        Iff(orbit, criterion)))));
    }

    private static Formula And(Formula slopeS, Formula slopeT, Formula xs, Formula xt) =>
        new Formula.Logic(
            Parenthesized(new Formula.Relation(slopeS, FormulaRelationOperator.Equal, slopeT)),
            FormulaLogicOperator.And,
            Parenthesized(new Formula.Bind(
                    FormulaQuantifier.Exists, FormulaIdentifier.Create("h"), Call("ZMod", F.Id("p")),
                new Formula.Relation(xs,
                    FormulaRelationOperator.Equal,
                    Call("translate", F.Id("h"), xt)))));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
