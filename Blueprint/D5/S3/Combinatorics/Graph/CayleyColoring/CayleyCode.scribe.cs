using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeCayleyCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting the cyclic vertices at an anchor transforms a target function into a rooted tree without changing its target multiset.",
        H("A Cayley code preserving targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("preserves-targets"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets"),
                H("The code preserves every target"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The code sends a function on the vertices other than the anchor to a rooted tree. It retains the arcs outside the cyclic core and replaces the core cycles by an anchor-first path to the root. A coordinate equivalence matches the original domain to the non-root vertices, including when the core is a singleton."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-core-anchored"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Anchored"),
                H("Anchored"),
                StatementSource.FromAuthor(Disp(CayleyCoreAnchored())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-core-away"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.CoreAway"),
                H("Core Away"),
                StatementSource.FromAuthor(Disp(CayleyCoreCoreaway())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-fixed-perm"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.FixedPerm"),
                H("Fixed Perm"),
                StatementSource.FromAuthor(Disp(CayleyCoreFixedperm())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-frame"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Frame"),
                H("Frame"),
                StatementSource.FromAuthor(Disp(CayleyCoreFrame())),
                AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(Disp(CayleyCoreFrameConstructor1()))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-frame-anchor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.anchor"),
                H("Anchor"),
                StatementSource.FromAuthor(Disp(CayleyCoreFrameAnchor())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The frame regards the distinguished vertex as an element of its core."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-frame-of-function"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.ofFunction"),
                H("Of Function"),
                StatementSource.FromAuthor(Disp(CayleyCoreFrameOffunction())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-frame-patch"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.patch"),
                H("Patch"),
                StatementSource.FromAuthor(Disp(CayleyCoreFramePatch())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-orders-of-length"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.OrdersOfLength"),
                H("Orders Of Length"),
                StatementSource.FromAuthor(Disp(CayleyCoreOrdersoflength())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-outside"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Outside"),
                H("Outside"),
                StatementSource.FromAuthor(Disp(CayleyCoreOutside())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-path-data"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.PathData"),
                H("Path Data"),
                StatementSource.FromAuthor(Disp(CayleyCorePathdata())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-code-coordinates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.codeCoordinates"),
                H("Code Coordinates"),
                StatementSource.FromAuthor(Disp(CayleyCoreCodecoordinates())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-from-inside"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromInside"),
                H("From Inside"),
                StatementSource.FromAuthor(Disp(CayleyCoreFrominside())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-from-outside"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromOutside"),
                H("From Outside"),
                StatementSource.FromAuthor(Disp(CayleyCoreFromoutside())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-index-before-last"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.indexBeforeLast"),
                H("Index Before Last"),
                StatementSource.FromAuthor(Disp(CayleyCoreIndexbeforelast())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-orbit-core"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitCore"),
                H("Orbit Core"),
                StatementSource.FromAuthor(Disp(CayleyCoreOrbitcore())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-orbit-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitEquiv"),
                H("Orbit Equiv"),
                StatementSource.FromAuthor(Disp(CayleyCoreOrbitequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-path-join"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathJoin"),
                H("Path Join"),
                StatementSource.FromAuthor(Disp(CayleyCorePathjoin())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-path-root"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathRoot"),
                H("Path Root"),
                StatementSource.FromAuthor(Disp(CayleyCorePathroot())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-path-self"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSelf"),
                H("Path Self"),
                StatementSource.FromAuthor(Disp(CayleyCorePathself())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-path-split"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSplit"),
                H("Path Split"),
                StatementSource.FromAuthor(Disp(CayleyCorePathsplit())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-rooted-code"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode"),
                H("Rooted Code"),
                StatementSource.FromAuthor(Disp(CayleyCoreRootedcode())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-core-successor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.successor"),
                H("Successor"),
                StatementSource.FromAuthor(Disp(CayleyCoreSuccessor())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var a = F.Id("a");
        var i = F.Id("i");
        var f = F.Id("f");
        var code = At(Call("rootedCode", a), f);
        var coordinate = At(Call("codeCoordinates", a, f), i);
        var target = Call("parent", Call("snd", code), Call("fst", code), coordinate);
        var away = Call("Away", v, a);
        return All("V", F.Id("Type"), Seq(Instance("Finite", v), All("a", v,
            All("f", Arrow(away, v), All("i", away, Equal(target, At(f, i)))))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula CayleyCoreAnchored() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Anchored"), Sp,
        F.Id("V"), Sp, F.Id("a"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("f"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, F.Id("f"), Sp,
        F.Id("a"), Sp, Eq, Sp, F.Id("a"), Sp, CloseBrace);

    private static Formula CayleyCoreCoreaway() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Close, Comma, Sp, Open, DefinitionDsl.Id("CoreAway"), Sp, F.Id("V"), Sp,
        F.Id("a"), Sp, F.Id("F"), Sp, F.Id("p"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"), Sp,
        Sp, Bar, Sp, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"), Sp, CloseBrace);

    private static Formula CayleyCoreFixedperm() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("FixedPerm"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close,
        Sp, Eq, Sp, OpenBrace, Sp, F.Id("e"), Sp, Colon, Sp, DefinitionDsl.Id("Equiv"), Dot,
        DefinitionDsl.Id("Perm"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"),
        Sp, Sp, Bar, Sp, Sp, F.Id("e"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("anchor"), Sp, Eq, Sp,
        F.Id("F"), Dot, DefinitionDsl.Id("anchor"), Sp, CloseBrace);

    private static Formula CayleyCoreFrameConstructor1() =>
        Seq(
        OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, To, Sp, OpenBrace,
        F.Id("a"), Sp, Colon, Sp, F.Id("V"), CloseBrace, Sp, To, Sp, Open, DefinitionDsl.Id("core"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Sp, To, Sp, F.Id("a"), Sp, InMacro, Sp,
        DefinitionDsl.Id("core"), Sp, To, Sp, Open, DefinitionDsl.Id("outside"), Sp, Colon, Sp, F.Id("V"),
        Sp, To, Sp, F.Id("V"), Close, Sp, To, Sp, Open, Forall, Sp, F.Id("x"), Sp, InMacro, Sp,
        DefinitionDsl.Id("core"), Comma, Sp, DefinitionDsl.Id("outside"), Sp, F.Id("x"), Sp, Eq, Sp,
        F.Id("x"), Close, Sp, To, Sp, Open, Forall, Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close,
        Comma, Sp, Exists, Sp, Open, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma,
        Sp, DefinitionDsl.Id("outside"), Caret, OpenBracket, F.Id("n"), CloseBracket, Sp, F.Id("x"), Sp,
        InMacro, Sp, DefinitionDsl.Id("core"), Close, Sp, To, Sp, DefinitionDsl.Id("CayleyCore"), Dot,
        DefinitionDsl.Id("Frame"), Sp, F.Id("a"));

    private static Formula CayleyCoreFrame() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("Frame"), Sp, F.Id("V"),
        Sp, F.Id("a"), Sp, Colon, Sp, DefinitionDsl.Id("Type"));

    private static Formula CayleyCoreFrameAnchor() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("anchor"), Sp, F.Id("F"), Close, Sp, Eq, Sp,
        F.Id("a"));

    private static Formula CayleyCoreFrameOffunction() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        F.Id("V"), Sp, To, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("C"), Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("ha"),
        Colon, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("C"), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"),
        Colon, Sp, Forall, Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, Exists, Sp,
        Open, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, F.Id("f"), Caret,
        OpenBracket, F.Id("n"), CloseBracket, Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("C"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("ofFunction"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("f"), Sp, F.Id("C"),
        Sp, DefinitionDsl.Id("ha"), Sp, F.Id("h"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot,
        DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Sp, Eq, Sp, DefinitionDsl.Id("let"), Sp, F.Id("g"),
        Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close,
        Sp, Mapsto, Sp, DefinitionDsl.Id("if"), Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("C"), Sp,
        DefinitionDsl.Id("then"), Sp, F.Id("x"), Sp, DefinitionDsl.Id("else"), Sp, F.Id("f"), Sp, F.Id("x"),
        Semi, Sp, OpenBrace, Sp, DefinitionDsl.Id("core"), Sp, Colon, Eq, Sp, F.Id("C"), Comma, Sp,
        DefinitionDsl.Id("anchor"), Mathrm, Grp(F.Id("anonymous")), DefinitionDsl.Id("mem"), Sp, Colon, Eq,
        Sp, DefinitionDsl.Id("ha"), Comma, Sp, DefinitionDsl.Id("outside"), Sp, Colon, Eq, Sp, F.Id("g"),
        Sp, CloseBrace);

    private static Formula CayleyCoreFramePatch() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("g"), Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Sp, To, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Close, Comma, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("patch"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp,
        F.Id("g"), Sp, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("if"), Sp,
        DefinitionDsl.Id("hx"), Sp, Colon, Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Sp, DefinitionDsl.Id("then"), Sp, DefinitionDsl.Id("val"), Sp, Open,
        F.Id("g"), Sp, Langle, Sp, F.Id("x"), Comma, Sp, DefinitionDsl.Id("hx"), Rangle, Sp, Close, Sp,
        DefinitionDsl.Id("else"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("outside"), Sp, F.Id("x"));

    private static Formula CayleyCoreOrdersoflength() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("OrdersOfLength"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, F.Id("m"), Sp,
        Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"),
        Close, Close, Sp, Eq, Sp, OpenBrace, Sp, F.Id("e"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp,
        Open, F.Id("m"), Sp, Plus, Sp, D(1), Close, Sp, Equiv, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"),
        Dot, DefinitionDsl.Id("core"), Sp, Sp, Bar, Sp, Sp, F.Id("e"), Sp, D(0), Sp, Eq, Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("anchor"), Sp, CloseBrace);

    private static Formula CayleyCoreOutside() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("Outside"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close,
        Sp, Eq, Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, F.Id("x"), Sp,
        Neg, Sp, InMacro, Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"), Sp, CloseBrace);

    private static Formula CayleyCorePathdata() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("PathData"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close,
        Sp, Eq, Sp, Open, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Times, Sp,
        OpenBrace, Sp, F.Id("e"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, Open, F.Id("m"), Sp, Plus, Sp,
        D(1), Close, Sp, Equiv, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"),
        Sp, Sp, Bar, Sp, Sp, F.Id("e"), Sp, D(0), Sp, Eq, Sp, F.Id("F"), Dot, DefinitionDsl.Id("anchor"),
        Sp, CloseBrace);

    private static Formula CayleyCoreCodecoordinates() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp, To, Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("codeCoordinates"), Sp, F.Id("V"), Sp,
        F.Id("a"), Sp, F.Id("f"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp, Equiv, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, Open, Open, DefinitionDsl.Id("rootedCode"), Sp, F.Id("a"), Close, Sp,
        F.Id("f"), Close, Dot, DefinitionDsl.Id("fst"), Close, Sp, Eq, Sp, DefinitionDsl.Id("have"), Sp,
        F.Id("d"), Sp, Colon, Eq, Sp, Open, DefinitionDsl.Id("cyclicEquiv"), Sp, F.Id("a"), Close, Sp, Open,
        Open, DefinitionDsl.Id("extendAnchor"), Sp, F.Id("a"), Close, Sp, F.Id("f"), Close, Semi, Sp,
        DefinitionDsl.Id("matchedCoordinates"), Sp, F.Id("d"), Dot, DefinitionDsl.Id("snd"), Sp, Open, Open,
        DefinitionDsl.Id("permPathEquiv"), Sp, F.Id("d"), Dot, DefinitionDsl.Id("fst"), Close, Sp,
        F.Id("d"), Dot, DefinitionDsl.Id("snd"), Close);

    private static Formula CayleyCoreFrominside() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Close, Comma, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("CoreAway"), Sp, F.Id("p"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("fromInside"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, F.Id("p"),
        Sp, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("p"), Close, Sp, Eq, Sp, Langle, Sp, DefinitionDsl.Id("coe"), Sp,
        F.Id("x"), Rangle);

    private static Formula CayleyCoreFromoutside() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("core"), Close, Comma, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Outside"), Sp, F.Id("F"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("fromOutside"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, F.Id("p"),
        Sp, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("p"), Close, Sp, Eq, Sp, Langle, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("x"), Rangle);

    private static Formula CayleyCoreIndexbeforelast() =>
        Seq(
        Forall, Sp, Open, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("indexBeforeLast"), Sp, F.Id("m"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp,
        F.Id("m"), Sp, Equiv, Sp, OpenBrace, Sp, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp,
        Open, F.Id("m"), Sp, Plus, Sp, D(1), Close, Sp, Sp, Bar, Sp, Sp, F.Id("i"), Sp, Neq, Sp,
        DefinitionDsl.Id("Fin"), Dot, DefinitionDsl.Id("last"), Sp, F.Id("m"), Sp, CloseBrace, Close, Sp,
        Eq, Sp, DefinitionDsl.Id("let"), Sp, F.Id("f"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp,
        Open, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Close, Sp, Mapsto, Sp,
        Langle, Sp, F.Id("i"), Dot, DefinitionDsl.Id("castSucc"), Rangle, Sp, Semi, Sp,
        DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("ofBijective"), Sp, F.Id("f"));

    private static Formula CayleyCoreOrbitcore() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("orbitCore"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("r"), Sp, F.Id("f"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Sp, Eq, Sp, OpenBrace, F.Id("x"), Sp,
        Colon, Sp, F.Id("V"), Sp, Bar, Sp, DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("Hits"),
        Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("f"), Close, Sp, F.Id("a"), Sp, F.Id("x"), CloseBrace);

    private static Formula CayleyCoreOrbitequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("orbitEquiv"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("r"), Sp, F.Id("f"),
        Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, Open, DefinitionDsl.Id("depth"), Sp, F.Id("r"), Sp,
        F.Id("f"), Sp, F.Id("a"), Sp, Plus, Sp, D(1), Close, Sp, Equiv, Sp, DefinitionDsl.Id("val"), Sp,
        Open, DefinitionDsl.Id("orbitCore"), Sp, F.Id("a"), Sp, F.Id("f"), Close, Close, Sp, Eq, Sp,
        DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("ofBijective"), Sp, Open, DefinitionDsl.Id("fun"),
        Sp, Open, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, Open, DefinitionDsl.Id("depth"),
        Sp, F.Id("r"), Sp, F.Id("f"), Sp, F.Id("a"), Sp, Plus, Sp, D(1), Close, Close, Sp, Mapsto, Sp,
        Langle, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("f"), Close, Caret, OpenBracket,
        DefinitionDsl.Id("val"), Sp, F.Id("i"), CloseBracket, Sp, F.Id("a"), Rangle, Sp, Close);

    private static Formula CayleyCorePathjoin() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"), Colon, Sp,
        Open, F.Id("F"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp,
        F.Id("a"), Close, Sp, Times, Sp, DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("PathData"),
        Sp, F.Id("F"), Close, Comma, Sp, Open, DefinitionDsl.Id("pathJoin"), Sp, F.Id("V"), Sp, F.Id("a"),
        Sp, F.Id("d"), Sp, Colon, Sp, Open, F.Id("r"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Times, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Sp, Eq,
        Sp, DefinitionDsl.Id("Sigma"), Dot, DefinitionDsl.Id("casesOn"), Sp, F.Id("d"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("F"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot,
        DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Sp, Open, F.Id("p"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("PathData"), Sp, F.Id("F"), Close, Sp, Eq, Gt,
        Sp, DefinitionDsl.Id("let"), Sp, F.Id("r"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("pathRoot"), Sp,
        F.Id("p"), Semi, Sp, DefinitionDsl.Id("let"), Sp, F.Id("f"), Sp, Colon, Eq, Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("patch"), Sp, Open, DefinitionDsl.Id("pathSelf"), Sp, F.Id("p"), Close, Semi, Sp,
        Langle, Sp, DefinitionDsl.Id("val"), Sp, F.Id("r"), Comma, Sp, Langle, Sp, F.Id("f"), Rangle, Sp,
        Rangle);

    private static Formula CayleyCorePathroot() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot,
        DefinitionDsl.Id("PathData"), Sp, F.Id("F"), Close, Comma, Sp, Open, DefinitionDsl.Id("pathRoot"),
        Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, F.Id("p"), Sp, Colon, Sp, DefinitionDsl.Id("val"),
        Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"), Close, Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("p"), Dot, DefinitionDsl.Id("snd"), Sp, Open, DefinitionDsl.Id("Fin"), Dot,
        DefinitionDsl.Id("last"), Sp, F.Id("p"), Dot, DefinitionDsl.Id("fst"), Close);

    private static Formula CayleyCorePathself() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("a"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot,
        DefinitionDsl.Id("PathData"), Sp, F.Id("F"), Close, Comma, Sp, Forall, Sp, Open, F.Id("x"), Colon,
        Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("pathSelf"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("F"), Sp, F.Id("p"), Sp,
        F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("core"),
        Close, Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp, F.Id("p"), Dot, DefinitionDsl.Id("snd"), Sp, Open,
        DefinitionDsl.Id("successor"), Sp, F.Id("p"), Dot, DefinitionDsl.Id("fst"), Sp, Open, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("p"), Dot, DefinitionDsl.Id("snd"), Close, Dot,
        DefinitionDsl.Id("symm"), Sp, F.Id("x"), Close, Close);

    private static Formula CayleyCorePathsplit() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"), Colon, Sp,
        Open, F.Id("r"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Times, Sp, DefinitionDsl.Id("CayleyParent"),
        Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("pathSplit"), Sp, F.Id("V"), Sp, F.Id("a"), Sp, F.Id("d"), Sp, Colon, Sp, Open,
        F.Id("F"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Sp,
        F.Id("a"), Close, Sp, Times, Sp, DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("PathData"),
        Sp, F.Id("F"), Close, Sp, Eq, Sp, DefinitionDsl.Id("let"), Sp, F.Id("F"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("CayleyCore"), Dot, DefinitionDsl.Id("Frame"), Dot, DefinitionDsl.Id("ofFunction"),
        Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("d"), Dot, DefinitionDsl.Id("snd"), Close, Sp, Open,
        DefinitionDsl.Id("orbitCore"), Sp, F.Id("a"), Sp, F.Id("d"), Dot, DefinitionDsl.Id("snd"), Close,
        Semi, Sp, Langle, Sp, F.Id("F"), Comma, Sp, Langle, Sp, DefinitionDsl.Id("depth"), Sp, F.Id("d"),
        Dot, DefinitionDsl.Id("fst"), Sp, F.Id("d"), Dot, DefinitionDsl.Id("snd"), Sp, F.Id("a"), Comma, Sp,
        Langle, Sp, DefinitionDsl.Id("orbitEquiv"), Sp, F.Id("a"), Sp, F.Id("d"), Dot,
        DefinitionDsl.Id("snd"), Rangle, Sp, Rangle, Sp, Rangle);

    private static Formula CayleyCoreRootedcode() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("rootedCode"), Sp, F.Id("V"), Sp, F.Id("a"), Sp,
        Colon, Sp, Open, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("a"), Sp,
        To, Sp, F.Id("V"), Close, Sp, Equiv, Sp, Open, Mathrm, Grp(F.Id("anonymous")), Sp, Colon, Sp,
        F.Id("V"), Close, Sp, Times, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("extendAnchor"), Sp, F.Id("a"), Close, Dot,
        DefinitionDsl.Id("trans"), Sp, Open, Open, DefinitionDsl.Id("cyclicEquiv"), Sp, F.Id("a"), Close,
        Dot, DefinitionDsl.Id("trans"), Sp, Open, Open, DefinitionDsl.Id("Equiv"), Dot,
        DefinitionDsl.Id("sigmaCongrRight"), Sp, DefinitionDsl.Id("permPathEquiv"), Close, Dot,
        DefinitionDsl.Id("trans"), Sp, Open, Open, DefinitionDsl.Id("pathEquiv"), Sp, F.Id("a"), Close, Dot,
        DefinitionDsl.Id("symm"), Dot, DefinitionDsl.Id("trans"), Sp, DefinitionDsl.Id("nativeRootedEquiv"),
        Dot, DefinitionDsl.Id("symm"), Close, Close, Close);

    private static Formula CayleyCoreSuccessor() =>
        Seq(
        Forall, Sp, Open, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("i"), Colon, Sp, DefinitionDsl.Id("Fin"), Sp, Open, F.Id("m"), Sp, Plus, Sp, D(1), Close,
        Close, Comma, Sp, Open, DefinitionDsl.Id("successor"), Sp, F.Id("m"), Sp, F.Id("i"), Sp, Colon, Sp,
        DefinitionDsl.Id("Fin"), Sp, Open, F.Id("m"), Sp, Plus, Sp, D(1), Close, Close, Sp, Eq, Sp, Langle,
        Sp, DefinitionDsl.Id("min"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("i"), Sp, Plus, Sp, D(1),
        Close, Sp, F.Id("m"), Rangle);
}
