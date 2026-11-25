using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class TransversalNineGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/WernerHolevo/";
    private const string Module = Prefix + "TransversalNineGluing";
    private static LibraryNoteRef Girard =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/girard2022mixedunitaryrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transversal gluing and conditional attainment of the symmetric Werner–Holevo rank in powers of three.",
        H("Transversal gluing of symmetric unitary bases"),
        Blocks(
            Describe.Lean(DescribeId.Create("glue-transversal-design"),
                DeclarationHandle.Create(Module + ".glueTD"),
                H("Gluing across nine fibers"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("m"), Gt, D(0), Comma, Quad, D(3), Sp, Mid, Sp, F.Id("m"), Comma, Quad,
                    Call("HasBasis", F.Id("m")), Comma, Quad, Call("TD", D(9), F.Id("m")), Quad,
                    Longrightarrow, Quad, Call("HasBasis", Seq(D(9), F.Id("m")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "HasBasis denotes a Hilbert–Schmidt orthogonal basis of the entire complex symmetric matrix space "
                        + "whose basis matrices are unitary. The supplied resolvable transversal design on nine fibers "
                        + "of size m has m parallel classes with m blocks each. Each block meets every fiber once. "
                        + "Each pair of vertices in distinct fibers occurs together in exactly one class.")),
                    Paragraph(DefinitionDsl.Text(
                        "Character phases on the seed matrices fill the entries within fibers, including the diagonal. "
                        + "The hypothesis that three divides m gives a partition of each class into triples of blocks. "
                        + "The labeling "),
                        Ref(Prefix + "TransversalNineLabels.edgeLabel_bijective"),
                        DefinitionDsl.Text(
                        " supplies the hollow orthogonal unitaries on a triple. Characters handle repetition across the "
                        + "triples. The class supports are disjoint and the resulting family has (9m)(9m+1)/2 matrices, "
                        + "the dimension of the symmetric matrix space in order 9m."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("affine-transversal-design"),
                DeclarationHandle.Create(Module + ".affineTD"),
                H("Transversal classes over a field"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("B", F.Id("s"), F.Id("t")), Eq, OpenBrace,
                    Open, F.Id("j"), Comma, F.Id("s"), Call("a", F.Id("j")), Plus, F.Id("t"), Close,
                    Sp, Mid, Sp, F.Id("j"), Sp, InMacro, Sp,
                    new Formula.Subscript(Seq(Mathbb, Grp(F.Id("F"))), D(9)),
                    CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Choose nine distinct field elements a(j). For each field element s, the intercept t ranges over "
                    + "the field and the displayed transversals partition the vertices. A pair from different fibers "
                    + "determines s and t uniquely by solving the two linear equations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("power-three-basis-step"),
                DeclarationHandle.Create(Module + ".primePowerStep"),
                H("A basis in order 3^r extends to order 3^(r+2)"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("r"), Geq, D(2), Comma, Quad, Call("HasBasis", PowerThree(F.Id("r"))), Quad,
                    Longrightarrow, Quad, Call("HasBasis", PowerThree(Seq(F.Id("r"), Plus, D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The field of order 3^r has at least nine elements, which supplies distinct slopes. Three divides its "
                    + "order, so the gluing construction applies to the supplied basis in that dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-from-basis"),
                DeclarationHandle.Create(Module + ".rank_exact"),
                H("Exact mixed-unitary rank from a full basis"),
                StatementSource.FromAuthor(Disp(RankStatement(Seq(
                    F.Id("n"), Gt, D(0), Comma, Quad, Call("HasBasis", F.Id("n")))))),
                AssessedProvenance.FromRepo(Girard),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The basis gives a uniform mixture of unitary conjugations with the displayed action. "
                    + "The Choi rank is a lower bound on the length of every finite decomposition with nonnegative real weights "
                    + "summing to one. Together with the field step, this gives the rank at n = 3^(r+2) whenever "
                    + "r is at least two and a full basis is supplied at 3^r."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-in-powers-of-three"),
                DeclarationHandle.Create(Module + ".mixedUnitaryRank_power_three"),
                H("Rank in powers of three from the order-27 seed"),
                StatementSource.FromAuthor(Disp(RankStatement(Seq(
                    Call("HasBasis", D(2, 7)), Comma, Quad, Sp, F.Id("n"), Eq, PowerThree(F.Id("r")),
                    Comma, Quad, Sp, F.Id("r"), Geq, D(3))))),
                AssessedProvenance.FromRepo(Girard),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "The hypothesis is a full Hilbert–Schmidt orthogonal basis of 378 symmetric unitary matrices "
                        + "in order 27. Induction applies the field step to each odd exponent beginning at three. "
                        + "For even r, write r = 2d with d at least two and apply "),
                        Ref(Prefix + "AffineNineWernerHolevo.mixedUnitaryRank_power_nine"),
                        DefinitionDsl.Text(".")),
                    Paragraph(DefinitionDsl.Text(
                        "Ma obtains the order-27 basis by an external Krawczyk interval computation. The Lean theorem "
                        + "takes the basis as an explicit hypothesis. The Girard literature note gives the locator for Ma’s certificate."))),
                DescribeRole.Theorem))));

    private static Formula PowerThree(Formula r) => new Formula.Power(D(3), r);

    private static Formula RankStatement(Formula hypotheses)
    {
        var n = F.Id("n");
        var x = F.Id("X");
        var phi = new Formula.Power(Phi, Plus);
        var matrices = new Formula.Subscript(F.Id("M"), n);
        return new Formula.Aligned([
            Seq(hypotheses, Amp),
            Seq(phi, Open, x, Close, Amp, Eq,
                new Formula.Fraction(Seq(Call("tr", x), F.Id("I"), Plus, new Formula.Power(x, F.Id("T"))),
                    Seq(n, Plus, D(1))),
                Comma, Quad, Forall, Sp, x, Sp, InMacro, Sp, matrices, Open, Mathbb, Grp(F.Id("C")), Close),
            Seq(Call("murank", phi), Amp, Eq,
                new Formula.Fraction(Seq(n, Open, n, Plus, D(1), Close), D(2))),
        ]);
    }
}
