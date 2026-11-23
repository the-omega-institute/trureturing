using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeFiniteLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sequential move count has the same finite law as the number of occupied ordinary bins.",
        H("Exact colored Cayley-tree move-count law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-sizes"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy"),
                H("Count law at every positive size"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("The source numerator sums the weights of legal terminal histories at a given length over every rooted tree and initial coloring. The denominator is the number of uniform ranking and colored-tree samples. On the other side the numerator counts words with the given occupancy, and the denominator counts all marked words. The anchor is zero, and a bin survives a throw exactly when its mark in the additive color group is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-exact-audit-sample-spaces-positive"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sample_spaces_positive"),
                H("Sample spaces positive"),
                StatementSource.FromAuthor(Disp(CayleyExactAuditSampleSpacesPositive())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-exact-audit-source-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sourceCount"),
                H("Source Count"),
                StatementSource.FromAuthor(Disp(CayleyExactAuditSourcecount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-throw"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throw"),
                H("Throw"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawThrow())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-throws"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throws"),
                H("Throws"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawThrows())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-bin"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin"),
                H("Bin"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawBin())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-bin-none-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_card"),
                H("Bin none card"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawBinNoneCard())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-bin-none-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_iff"),
                H("Bin none iff"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawBinNoneIff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-bin-some-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_card"),
                H("Bin some card"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawBinSomeCard())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-bin-some-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_iff"),
                H("Bin some iff"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawBinSomeIff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-cardinality-nonzero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.cardinality_nonzero"),
                H("Cardinality nonzero"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawCardinalityNonzero())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-coded-draw-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.codedDrawEquiv"),
                H("Coded Draw Equiv"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawCodeddrawequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-frequency"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.frequency"),
                H("Frequency"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawFrequency())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-finite-law-occupied"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.occupied"),
                H("Occupied"),
                StatementSource.FromAuthor(Disp(CayleyFiniteLawOccupied())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-native-law-terminal"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Terminal"),
                H("Terminal"),
                StatementSource.FromAuthor(Disp(CayleyNativeLawTerminal())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-native-law-total-numerator"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.TotalNumerator"),
                H("Total Numerator"),
                StatementSource.FromAuthor(Disp(CayleyNativeLawTotalnumerator())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-native-law-total-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.totalEquiv"),
                H("Total Equiv"),
                StatementSource.FromAuthor(Disp(CayleyNativeLawTotalequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-reduction-colored"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Colored"),
                H("Colored"),
                StatementSource.FromAuthor(Disp(CayleyReductionColored())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-reduction-edge-draw"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.EdgeDraw"),
                H("Edge Draw"),
                StatementSource.FromAuthor(Disp(CayleyReductionEdgedraw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-reduction-parent-draw"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.ParentDraw"),
                H("Parent Draw"),
                StatementSource.FromAuthor(Disp(CayleyReductionParentdraw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-reduction-marked-at"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.markedAt"),
                H("Marked At"),
                StatementSource.FromAuthor(Disp(CayleyReductionMarkedat())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-reduction-recolor-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.recolorCount"),
                H("Recolor Count"),
                StatementSource.FromAuthor(Disp(CayleyReductionRecolorcount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var p = F.Id("P");
        var e = F.Id("e");
        var j = F.Id("j");
        var v = Call("Fin", n);
        var a = D(0);
        var colored = Call("Colored", v, Call("ZMod", k));
        var spell = Call("Throws", a, Call("ZMod", k));
        var den = Call("card", Call("SourceSample", n, k));
        var urnDen = Call("card", spell);
        var moved = Call("card", Call("TotalNumerator", e, p, j));
        var hit = Call("frequency", spell, F.Id("occupied"), j);
        var sizes = Equal(Call("card", Call("Away", a)), Subtract(n, D(1)));
        var microstates = Equal(Call("card", Call("Throw", v, Call("ZMod", k))), Multiply(n, k));
        var some = All("b", v, Equal(Call("card", Call("BinFiber", Call("some", F.Id("b")))), D(1)));
        var none = Equal(Call("card", Call("BinFiber", F.Id("none"))), Multiply(n, Subtract(k, D(1))));
        var law = Seq(Equal(Multiply(moved, urnDen), Multiply(hit, den)), Sp, Land, Sp,
            D(0), Lt, den, Sp, Land, Sp, D(0), Lt, urnDen, Sp, Land, Sp, sizes, Sp,
            Land, Sp, microstates, Sp, Land, Sp, Open, some, Close, Sp, Land, Sp, none);
        var parameters = All("K", F.Id("Type"), All("e", Call("Embedding", Call("ZMod", k), F.Id("K")),
            All("P", Seq(Open, F.Id("s"), Colon, Sp, colored, Close, Sp, To, Sp,
                Call("FreePolicy", F.Id("K"), Call("graph", F.Id("s")))), All("j", Nat, law))));
        return All("n", Nat, All("k", Nat,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, parameters)));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula CayleyExactAuditSampleSpacesPositive() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("k"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("hk"),
        Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("anchor"), Colon, Sp, F.Id("V"), Close, Comma, Sp, D(0), Sp, Lt, Sp,
        DefinitionDsl.Id("Nat"), Dot, DefinitionDsl.Id("card"), Sp, Open, DefinitionDsl.Id("Equiv"), Dot,
        DefinitionDsl.Id("Perm"), Sp, F.Id("V"), Sp, Times, Sp, DefinitionDsl.Id("CayleyReduction"), Dot,
        DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"),
        Close, Close, Sp, Land, Sp, D(0), Sp, Lt, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, Open, DefinitionDsl.Id("CayleyFiniteLaw"), Dot,
        DefinitionDsl.Id("Throws"), Sp, DefinitionDsl.Id("anchor"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp,
        F.Id("k"), Close, Close);

    private static Formula CayleyExactAuditSourcecount() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("k"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("embed"), Colon, Sp, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Sp, Operatorname,
        Grp(F.Id("embeds")), Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp, Open, F.Id("s"), Colon, Sp,
        DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp, F.Id("V"), Sp, Times, Sp,
        DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open,
        DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Close, Close, Comma, Sp, Open,
        DefinitionDsl.Id("sourceCount"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("k"), Sp,
        DefinitionDsl.Id("embed"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq,
        Sp, Open, DefinitionDsl.Id("rankedHistory"), Sp, Open, DefinitionDsl.Id("conflict"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(2), Dot, D(1), Dot, D(2), Close, Sp, Open,
        DefinitionDsl.Id("coe"), Sp, DefinitionDsl.Id("embed"), Sp, Circ, Sp, F.Id("s"), Dot, D(2), Dot,
        D(2), Close, Close, Sp, F.Id("s"), Dot, D(1), Sp, DefinitionDsl.Id("Set"), Dot,
        DefinitionDsl.Id("univ"), Close, Dot, DefinitionDsl.Id("length"));

    private static Formula CayleyFiniteLawThrow() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"),
        Sp, Open, DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("w"), Close, Close, Sp, Eq, Sp,
        F.Id("V"), Sp, Times, Sp, F.Id("A"));

    private static Formula CayleyFiniteLawThrows() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("A"), Colon, Sp,
        DefinitionDsl.Id("Type"), Close, Comma, Sp, Open, DefinitionDsl.Id("Throws"), Sp, F.Id("V"), Sp,
        F.Id("a"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("w"), Close, Close, Sp, Eq, Sp,
        DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp, To, Sp,
        DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"));

    private static Formula CayleyFiniteLawBin() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp,
        DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("bin"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("a"), Sp,
        Colon, Sp, DefinitionDsl.Id("Option"), Sp, F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("if"), Sp,
        F.Id("a"), Dot, D(2), Sp, Eq, Sp, D(0), Sp, DefinitionDsl.Id("then"), Sp, DefinitionDsl.Id("some"),
        Sp, F.Id("a"), Dot, D(1), Sp, DefinitionDsl.Id("else"), Sp, DefinitionDsl.Id("none"));

    private static Formula CayleyFiniteLawBinNoneCard() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"),
        Sp, Sp, Bar, Sp, Sp, DefinitionDsl.Id("bin"), Sp, F.Id("x"), Sp, Eq, Sp, DefinitionDsl.Id("none"),
        Sp, CloseBrace, Sp, Eq, Sp, DefinitionDsl.Id("Nat"), Dot, DefinitionDsl.Id("card"), Sp, F.Id("V"),
        Sp, Cdot, Sp, DefinitionDsl.Id("Nat"), Dot, DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("c"),
        Sp, Colon, Sp, F.Id("A"), Sp, Sp, Bar, Sp, Sp, F.Id("c"), Sp, Neq, Sp, D(0), Sp, CloseBrace);

    private static Formula CayleyFiniteLawBinNoneIff() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, DefinitionDsl.Id("bin"), Sp, F.Id("x"), Sp, Eq, Sp, DefinitionDsl.Id("none"), Sp,
        Iff, Sp, F.Id("x"), Dot, D(2), Sp, Neq, Sp, D(0));

    private static Formula CayleyFiniteLawBinSomeCard() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("v"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("Nat"), Dot, DefinitionDsl.Id("card"), Sp, OpenBrace,
        Sp, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"),
        Sp, F.Id("V"), Sp, F.Id("A"), Sp, Sp, Bar, Sp, Sp, DefinitionDsl.Id("bin"), Sp, F.Id("x"), Sp, Eq,
        Sp, DefinitionDsl.Id("some"), Sp, F.Id("v"), Sp, CloseBrace, Sp, Eq, Sp, D(1));

    private static Formula CayleyFiniteLawBinSomeIff() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throw"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        DefinitionDsl.Id("bin"), Sp, F.Id("x"), Sp, Eq, Sp, DefinitionDsl.Id("some"), Sp, F.Id("v"), Sp,
        Iff, Sp, F.Id("x"), Dot, D(1), Sp, Eq, Sp, F.Id("v"), Sp, Land, Sp, F.Id("x"), Dot, D(2), Sp, Eq,
        Sp, D(0));

    private static Formula CayleyFiniteLawCardinalityNonzero() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("NeZero"), Sp, F.Id("k"), CloseBracket, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("c"), Sp, Colon, Sp, DefinitionDsl.Id("ZMod"), Sp,
        F.Id("k"), Sp, Sp, Bar, Sp, Sp, F.Id("c"), Sp, Neq, Sp, D(0), Sp, CloseBrace, Sp, Eq, Sp, F.Id("k"),
        Sp, Minus, Sp, D(1));

    private static Formula CayleyFiniteLawCodeddrawequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("codedDrawEquiv"), Sp, F.Id("V"), Sp, F.Id("A"),
        Sp, F.Id("a"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyFiniteLaw"), Dot, DefinitionDsl.Id("Throws"),
        Sp, F.Id("a"), Sp, F.Id("A"), Sp, Equiv, Sp, Open, F.Id("p"), Sp, Colon, Sp, F.Id("V"), Sp, Times,
        Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times,
        Sp, Open, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("p"), Dot, D(1),
        Sp, To, Sp, F.Id("A"), Close, Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("prodFunctions"), Sp, Open,
        DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Close, Sp,
        F.Id("V"), Sp, F.Id("A"), Close, Dot, DefinitionDsl.Id("trans"), Sp, Open, Open,
        DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("sigmaEquivProd"), Sp, Open,
        DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp, To, Sp,
        F.Id("V"), Close, Sp, Open, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp,
        F.Id("a"), Sp, To, Sp, F.Id("A"), Close, Close, Dot, DefinitionDsl.Id("symm"), Dot,
        DefinitionDsl.Id("trans"), Sp, Open, Open, Open, DefinitionDsl.Id("rootedCode"), Sp, F.Id("a"),
        Close, Dot, DefinitionDsl.Id("trans"), Sp, Open, DefinitionDsl.Id("Equiv"), Dot,
        DefinitionDsl.Id("sigmaEquivProd"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Close, Close, Dot, DefinitionDsl.Id("sigmaCongr"),
        Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("f"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"),
        Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp, To, Sp, F.Id("V"), Close, Sp, Eq, Gt, Sp, Open,
        DefinitionDsl.Id("codeCoordinates"), Sp, F.Id("a"), Sp, F.Id("f"), Close, Dot,
        DefinitionDsl.Id("arrowCongr"), Sp, Open, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("refl"),
        Sp, F.Id("A"), Close, Close, Close);

    private static Formula CayleyFiniteLawFrequency() =>
        Seq(
        Forall, Sp, Open, F.Id("X"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, F.Id("X"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("frequency"), Sp, F.Id("X"), Sp, F.Id("f"), Sp, F.Id("j"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp, F.Id("X"), Sp, Sp, Bar, Sp,
        Sp, F.Id("f"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("j"), Sp, CloseBrace);

    private static Formula CayleyFiniteLawOccupied() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket, DefinitionDsl.Id("Zero"),
        Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma,
        Sp, Forall, Sp, Open, F.Id("t"), Colon, Sp, DefinitionDsl.Id("CayleyFiniteLaw"), Dot,
        DefinitionDsl.Id("Throws"), Sp, F.Id("a"), Sp, F.Id("A"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("occupied"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("a"), Sp, F.Id("t"), Sp, Colon,
        Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("filterCard"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Eq, Gt, Sp,
        Exists, Sp, Open, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("a"), Close, Comma, Sp, DefinitionDsl.Id("bin"), Sp, Open,
        F.Id("t"), Sp, F.Id("i"), Close, Sp, Eq, Sp, DefinitionDsl.Id("some"), Sp, F.Id("v"));

    private static Formula CayleyNativeLawTerminal() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("policy"), Colon, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("G"), Close, Comma, Sp, Forall, Sp, Open, F.Id("c"), Colon,
        Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp, Open, F.Id("l"), Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Terminal"), Sp,
        F.Id("V"), Sp, F.Id("K"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("policy"), Sp, F.Id("c"), Sp,
        F.Id("l"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Exists, Sp, Open,
        DefinitionDsl.Id("final"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("policy"), Sp, OpenBracket, CloseBracket, Sp, F.Id("c"), Sp, F.Id("l"), Sp,
        DefinitionDsl.Id("final"), Sp, Land, Sp, Forall, Sp, Open, F.Id("v"), Sp, F.Id("w"), Sp, Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Neg, Sp, Open, DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("final"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"));

    private static Formula CayleyNativeLawTotalnumerator() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("k"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("embed"), Colon, Sp, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Sp, Operatorname,
        Grp(F.Id("embeds")), Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("policy"),
        Colon, Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyReduction"), Dot,
        DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"),
        Close, Close, Sp, To, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("FreePolicy"),
        Sp, DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(1), Dot, D(2), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("TotalNumerator"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("k"), Sp,
        DefinitionDsl.Id("embed"), Sp, DefinitionDsl.Id("policy"), Sp, F.Id("j"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Close, Sp, Eq, Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open,
        DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Close, Close, Sp, Times, Sp,
        DefinitionDsl.Id("CayleyNativeLaw"), Dot, DefinitionDsl.Id("NativeNumerator"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(1), Dot, D(2), Close, Sp, Open,
        DefinitionDsl.Id("policy"), Sp, F.Id("s"), Close, Sp, Open, DefinitionDsl.Id("coe"), Sp,
        DefinitionDsl.Id("embed"), Sp, Circ, Sp, F.Id("s"), Dot, D(2), Close, Sp, F.Id("j"));

    private static Formula CayleyNativeLawTotalequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("k"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("embed"), Colon, Sp, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Sp, Operatorname,
        Grp(F.Id("embeds")), Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("policy"),
        Colon, Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyReduction"), Dot,
        DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"),
        Close, Close, Sp, To, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("FreePolicy"),
        Sp, DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(1), Dot, D(2), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("totalEquiv"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("k"), Sp,
        DefinitionDsl.Id("embed"), Sp, DefinitionDsl.Id("policy"), Sp, F.Id("j"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyNativeLaw"), Dot, DefinitionDsl.Id("TotalNumerator"), Sp,
        DefinitionDsl.Id("embed"), Sp, DefinitionDsl.Id("policy"), Sp, F.Id("j"), Sp, Equiv, Sp, OpenBrace,
        Sp, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Sp, Times, Sp, DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp,
        F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Close, Sp, Sp, Bar, Sp, Sp,
        DefinitionDsl.Id("sourceCount"), Sp, DefinitionDsl.Id("embed"), Sp, F.Id("s"), Sp, Eq, Sp,
        F.Id("j"), Sp, CloseBrace, Close, Sp, Eq, Sp, DefinitionDsl.Id("let"), Sp, F.Id("H"), Sp, Colon, Eq,
        Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open,
        DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Close, Close, Sp, Eq, Gt, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("rank"), Sp, Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"),
        Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, DefinitionDsl.Id("sourceCount"), Sp, DefinitionDsl.Id("embed"),
        Sp, Open, DefinitionDsl.Id("rank"), Comma, Sp, F.Id("s"), Close, Sp, Eq, Sp, F.Id("j"), Sp,
        CloseBrace, Semi, Sp, Open, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("sigmaCongrRight"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyReduction"),
        Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"),
        Close, Close, Sp, Eq, Gt, Sp, DefinitionDsl.Id("conditionalEquiv"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(1), Dot, D(2), Close, Sp, Open,
        DefinitionDsl.Id("policy"), Sp, F.Id("s"), Close, Sp, Open, DefinitionDsl.Id("coe"), Sp,
        DefinitionDsl.Id("embed"), Sp, Circ, Sp, F.Id("s"), Dot, D(2), Close, Sp, F.Id("j"), Close, Dot,
        DefinitionDsl.Id("trans"), Sp, Open, DefinitionDsl.Id("id"), Sp, OpenBrace, Sp,
        DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp,
        Colon, Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyReduction"), Dot,
        DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open, DefinitionDsl.Id("ZMod"), Sp, F.Id("k"),
        Close, Close, Sp, Times, Sp, F.Id("H"), Sp, F.Id("s"), Close, Sp, Eq, Gt, Sp, Langle, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("x"), Dot, DefinitionDsl.Id("snd"), Comma, Sp, F.Id("x"), Dot,
        DefinitionDsl.Id("fst"), Close, Rangle, Sp, Comma, Sp, DefinitionDsl.Id("invFun"), Sp, Colon, Eq,
        Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("s"), Sp, Colon, Sp, OpenBrace, Sp, F.Id("s"), Sp,
        Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp, F.Id("V"), Sp, Times, Sp,
        DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, Open,
        DefinitionDsl.Id("ZMod"), Sp, F.Id("k"), Close, Sp, Sp, Bar, Sp, Sp,
        DefinitionDsl.Id("sourceCount"), Sp, DefinitionDsl.Id("embed"), Sp, F.Id("s"), Sp, Eq, Sp,
        F.Id("j"), Sp, CloseBrace, Close, Sp, Eq, Gt, Sp, Langle, Sp, Open, DefinitionDsl.Id("val"), Sp,
        F.Id("s"), Close, Dot, D(2), Comma, Sp, Langle, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("s"),
        Close, Dot, D(1), Rangle, Sp, Rangle, Sp, CloseBrace, Close);

    private static Formula CayleyReductionColored() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"),
        Sp, Open, DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("u"), Sp, F.Id("w"), Close, Close, Sp,
        Eq, Sp, Open, F.Id("V"), Sp, Times, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times, Sp, Open, F.Id("V"), Sp, To, Sp,
        F.Id("A"), Close);

    private static Formula CayleyReductionEdgedraw() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("EdgeDraw"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"),
        Sp, Open, DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("u"), Sp, F.Id("w"), Close, Close, Sp,
        Eq, Sp, Open, F.Id("p"), Sp, Colon, Sp, F.Id("V"), Sp, Times, Sp, DefinitionDsl.Id("CayleyProbe"),
        Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times, Sp, F.Id("A"), Sp, Times, Sp, Open,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("p"), Dot, D(2), Close, Dot,
        DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close);

    private static Formula CayleyReductionParentdraw() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("ParentDraw"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("u"), Sp,
        F.Id("w"), Close, Close, Sp, Eq, Sp, Open, F.Id("p"), Sp, Colon, Sp, F.Id("V"), Sp, Times, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times, Sp,
        F.Id("A"), Sp, Times, Sp, Open, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp,
        F.Id("p"), Dot, D(1), Sp, To, Sp, F.Id("A"), Close);

    private static Formula CayleyReductionMarkedat() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Open, DefinitionDsl.Id("markedAt"), Sp,
        F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("w"), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp,
        F.Id("V"), Sp, Times, Sp, F.Id("A"), Sp, Times, Sp, DefinitionDsl.Id("CayleyMarks"), Dot,
        DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"));

    private static Formula CayleyReductionRecolorcount() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("s"),
        Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp, F.Id("V"), Sp, Times, Sp,
        DefinitionDsl.Id("CayleyReduction"), Dot, DefinitionDsl.Id("Colored"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("recolorCount"), Sp, F.Id("V"), Sp, F.Id("A"), Sp,
        F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq, Sp, Open,
        DefinitionDsl.Id("rankedHistory"), Sp, Open, DefinitionDsl.Id("conflict"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(2), Dot, D(1), Dot, D(2), Close, Sp, F.Id("s"), Dot,
        D(2), Dot, D(2), Close, Sp, F.Id("s"), Dot, D(1), Sp, DefinitionDsl.Id("Set"), Dot,
        DefinitionDsl.Id("univ"), Close, Dot, DefinitionDsl.Id("length"));
}
