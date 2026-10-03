using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CollinearTripleFixedPointCensusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/CollinearTripleFixedPointCensus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-point census and the exact three-torsion residue for collinear triples.",
        H("Collinear Triple Fixed-Point Census"),
        Blocks(
            Paragraph(Text("A Triple is an unordered three-point set in the square grid "
                + "modulo n, with distinct first and second coordinates and zero difference "
                + "determinant. Translation is the additive group action on these sets.")),
            Node("card_fixedBy_three_torsion", "Exact count for an eligible translation",
                Disp(Seq(D(0), Sp, Lt, Sp, F.Id("n"), Comma, Sp,
                    D(3), Call("fst", F.Id("t")), Sp, Eq, Sp, D(0), Comma, Sp,
                    D(3), Call("snd", F.Id("t")), Sp, Eq, Sp, D(0), Comma, Sp,
                    Call("fst", F.Id("t")), Sp, Neq, Sp, D(0), Comma, Sp,
                    Call("snd", F.Id("t")), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
                    Call("card", Call("fixedBy", Call("Triple", F.Id("n")), F.Id("t"))),
                    Sp, Eq, Sp, new Formula.Fraction(new Formula.Power(F.Id("n"), D(2)), D(3)))),
                "If three times each coordinate of t is zero and neither coordinate is zero, "
                + "every triple fixed by t is a translate of {0,t,2t}. Conversely every such "
                + "translate is fixed. The canonical cycle has a three-element translation "
                + "stabilizer, so orbit-stabilizer gives exactly n squared divided by three "
                + "fixed triples. The statement requires a positive modulus."),
            Node("exact_three_torsion_residue", "Exact residue for multiples of three",
                Disp(Seq(D(0), Sp, Lt, Sp, F.Id("m"), Sp, Implies, Sp,
                    Exists, Sp, F.Id("q"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Call("card", Call("Triple", Seq(D(3), F.Id("m")))),
                    Sp, Eq, Sp, new Formula.Power(Seq(Open, D(3), F.Id("m"), Close), D(2)),
                    F.Id("q"), Sp, Plus, Sp, D(2),
                    new Formula.Fraction(
                        new Formula.Power(Seq(Open, D(3), F.Id("m"), Close), D(2)), D(3)))),
                "For n=3m, exactly four nonzero translations can fix a triple, and each "
                + "fixes n squared divided by three triples. Every other nonzero translation "
                + "fixes none; the identity fixes all A(n) triples. Burnside gives "
                + "A(n)+4n squared/3=n squared times the number of translation orbits. "
                + "That orbit count is at least two, yielding the displayed natural-number "
                + "formula with q equal to the orbit count minus two."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(("collinear-fixed-census-" + name.Replace('_', '-'))
                .ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
