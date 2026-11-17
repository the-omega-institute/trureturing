using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Descartes;

internal sealed class SplitPrimeSphereRadiiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared split-prime powers in primitive spherical Descartes radii.",
        H("The split-prime clause of A390148"),
        Blocks(Describe.Lean(
            DescribeId.Create("split-prime-sphere-radii"),
            DeclarationHandle.Create("D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result"),
            H("One or two other coordinates at every positive threshold"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/ArithUnits/hohn2025a390148")),
            Blocks(
                Paragraph(Text("The four radii are positive natural numbers with common gcd one. "
                    + "The reciprocal equation is over the rationals. Both i and j range over "
                    + "Fin(4), so equal radii count as separate coordinates. No ordering or "
                    + "pairwise coprimality is assumed. The exponent k is any positive natural number.")),
                Paragraph(Text("Use the least common multiple L and the integer curvatures b(i)=L/r(i) "
                    + "from PrimitiveSphereRadii. Their common gcd is one, and their sum squared "
                    + "equals three times the sum of their squares. If all coordinates other than "
                    + "i vanished modulo an odd prime p, primitivity would make b(i) nonzero. "
                    + "The equation would make twice the square of b(i) zero modulo p, a contradiction.")),
                Paragraph(Text("There is therefore a coordinate j distinct from i whose curvature "
                    + "is coprime to p. The identity b(a)r(a)=L gives "
                    + "v_p(b(a))+v_p(r(a))=v_p(L). Thus r(j) has at least the valuation of r(i), "
                    + "so it is divisible by p to the k. Common gcd one excludes divisibility "
                    + "of all four radii by this positive power. The number of other coordinates "
                    + "is consequently one or two. The separate inert-prime valuation, "
                    + "3-adic valuation, repetition and chain assertions are outside this statement."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hohn-a390148-split-prime-shared-divisibility"),
                ResolutionKind.Proved)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Ri(string name) => Seq(V("r"), Underscore, V(name));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula SumI(Formula x) => Seq(Sum, Underscore, V("i"), x);

    private static Formula MainFormula()
    {
        var reciprocal = Seq(Frac, Grp(D(1)), Grp(Ri("i")));
        var equation = Seq(Pow(Par(SumI(reciprocal)), D(2)), Eq,
            D(3), SumI(Pow(Par(reciprocal), D(2))));
        var fiber = Seq(OpenBrace, V("j"), InMacro, Operatorname, Grp(V("Fin")), Par(D(4)),
            Colon, V("j"), Neq, Sp, V("i"), Sp, Land, Sp,
            Pow(V("p"), V("k")), Mid, Sp, Ri("j"), CloseBrace);
        var count = Seq(Lvert, fiber, Rvert);
        return Disp(Seq(Forall, Sp, V("r"), Colon, Operatorname, Grp(V("Fin")), Par(D(4)),
            To, Mathbb, Grp(V("N")), Comma,
            Par(Seq(Par(Seq(Forall, Sp, V("i"), Comma, D(0), Lt, Ri("i"))), Sp, Land, Sp,
                Gcd, Par(V("r")), Eq, D(1), Sp, Land, Sp, equation)), Sp, Implies, Sp,
            Forall, Sp, V("p"), InMacro, Mathbb, Grp(V("N")), Comma,
            Par(Seq(Operatorname, Grp(V("Prime")), Par(V("p")), Sp, Land, Sp,
                V("p"), Operatorname, Grp(V("mod")), D(3), Eq, D(1))), Sp, Implies, Sp,
            Forall, Sp, V("k"), InMacro, Mathbb, Grp(V("N")), Comma,
            D(0), Lt, V("k"), Sp, Implies, Sp,
            Forall, Sp, V("i"), InMacro, Operatorname, Grp(V("Fin")), Par(D(4)), Comma,
            Pow(V("p"), V("k")), Mid, Sp, Ri("i"), Sp, Implies, Sp,
            Par(Seq(count, Eq, D(1), Sp, Lor, Sp, count, Eq, D(2)))));
    }
}
