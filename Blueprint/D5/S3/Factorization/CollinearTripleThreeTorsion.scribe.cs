using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CollinearTripleThreeTorsionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/CollinearTripleThreeTorsion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nontrivial symmetries of collinear triples have two cyclic directions.",
        H("Three-Torsion Directions of Collinear Triples"),
        Blocks(
            Paragraph(Text("A Triple is an unordered three-point subset of the square "
                + "grid modulo n, with distinct coordinates and zero difference determinant. "
                + "In the first and third statements n=3m and m is positive.")),
            Node("stabilizer_direction_four", "Four possible stabilizing vectors",
                Disp(Seq(Call("translate", T(), S()), Sp, Eq, Sp, S(), Comma, Sp,
                    T(), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
                    T(), Sp, InMacro, Sp, OpenBrace,
                    Pair(M(), M()), Comma, Sp, Pair(M(), TwoM()), Comma, Sp,
                    Pair(TwoM(), M()), Comma, Sp, Pair(TwoM(), TwoM()), CloseBrace)),
                "Summing the three points shows 3t=0. Distinct coordinates exclude a "
                + "zero coordinate of any nonzero stabilizer, leaving four vectors."),
            Node("three_cycle_collinear", "Order-three cycles are collinear triples",
                Disp(Seq(D(3), Call("fst", T()), Sp, Eq, Sp, D(0), Comma, Sp,
                    D(3), Call("snd", T()), Sp, Eq, Sp, D(0), Comma, Sp,
                    Call("fst", T()), Sp, Neq, Sp, D(0), Comma, Sp,
                    Call("snd", T()), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
                    Call("IsCollinearTriple", Cycle()))),
                "Both coordinates of t must be nonzero and annihilated by three. "
                + "The three points 0, t, and 2t then have distinct coordinates; "
                + "their difference determinants vanish."),
            Node("two_canonical_cycles_collinear", "Both standard directions occur",
                Disp(Seq(Call("IsCollinearTriple", CycleOf(Pair(M(), M()))),
                    Sp, Land, Sp,
                    Call("IsCollinearTriple", CycleOf(Pair(M(), TwoM()))))),
                "For each positive m, the two order-three vectors (m,m) and (m,2m) "
                + "produce admissible triples through the origin."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("collinear-three-torsion-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula S() => F.Id("S");
    private static Formula T() => F.Id("t");
    private static Formula Pair(Formula a, Formula b) =>
        Seq(Open, a, Comma, Sp, b, Close);
    private static Formula M() => F.Id("m");
    private static Formula TwoM() => Seq(D(2), M());
    private static Formula Cycle() => CycleOf(T());
    private static Formula CycleOf(Formula t) =>
        Seq(OpenBrace, D(0), Comma, Sp, t, Comma, Sp, D(2), t, CloseBrace);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
